import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fortyOneAMFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fortyOneAMFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fortyOneAMFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fortyOneAMFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fortyOneAMFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fortyOneAMFastPow a n * fortyOneAMFastPow a n * a
        else fortyOneAMFastPow a n * fortyOneAMFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fortyOneAM_2 : Nat.Prime 2 := by norm_num
private theorem prime_fortyOneAM_3 : Nat.Prime 3 := by norm_num
private theorem prime_fortyOneAM_5 : Nat.Prime 5 := by norm_num
private theorem prime_fortyOneAM_7 : Nat.Prime 7 := by norm_num
private theorem prime_fortyOneAM_11 : Nat.Prime 11 := by norm_num
private theorem prime_fortyOneAM_13 : Nat.Prime 13 := by norm_num
private theorem prime_fortyOneAM_17 : Nat.Prime 17 := by norm_num
private theorem prime_fortyOneAM_19 : Nat.Prime 19 := by norm_num
private theorem prime_fortyOneAM_23 : Nat.Prime 23 := by norm_num
private theorem prime_fortyOneAM_29 : Nat.Prime 29 := by norm_num
private theorem prime_fortyOneAM_31 : Nat.Prime 31 := by norm_num
private theorem prime_fortyOneAM_37 : Nat.Prime 37 := by norm_num
private theorem prime_fortyOneAM_41 : Nat.Prime 41 := by norm_num
private theorem prime_fortyOneAM_43 : Nat.Prime 43 := by norm_num
private theorem prime_fortyOneAM_47 : Nat.Prime 47 := by norm_num
private theorem prime_fortyOneAM_53 : Nat.Prime 53 := by norm_num
private theorem prime_fortyOneAM_59 : Nat.Prime 59 := by norm_num
private theorem prime_fortyOneAM_61 : Nat.Prime 61 := by norm_num
private theorem prime_fortyOneAM_67 : Nat.Prime 67 := by norm_num
private theorem prime_fortyOneAM_71 : Nat.Prime 71 := by norm_num
private theorem prime_fortyOneAM_73 : Nat.Prime 73 := by norm_num
private theorem prime_fortyOneAM_79 : Nat.Prime 79 := by norm_num
private theorem prime_fortyOneAM_83 : Nat.Prime 83 := by norm_num
private theorem prime_fortyOneAM_89 : Nat.Prime 89 := by norm_num
private theorem prime_fortyOneAM_97 : Nat.Prime 97 := by norm_num
private theorem prime_fortyOneAM_101 : Nat.Prime 101 := by norm_num
private theorem prime_fortyOneAM_103 : Nat.Prime 103 := by norm_num
private theorem prime_fortyOneAM_107 : Nat.Prime 107 := by norm_num
private theorem prime_fortyOneAM_109 : Nat.Prime 109 := by norm_num
private theorem prime_fortyOneAM_113 : Nat.Prime 113 := by norm_num
private theorem prime_fortyOneAM_127 : Nat.Prime 127 := by norm_num
private theorem prime_fortyOneAM_131 : Nat.Prime 131 := by norm_num
private theorem prime_fortyOneAM_137 : Nat.Prime 137 := by norm_num
private theorem prime_fortyOneAM_139 : Nat.Prime 139 := by norm_num
private theorem prime_fortyOneAM_149 : Nat.Prime 149 := by norm_num
private theorem prime_fortyOneAM_157 : Nat.Prime 157 := by norm_num
private theorem prime_fortyOneAM_163 : Nat.Prime 163 := by norm_num
private theorem prime_fortyOneAM_167 : Nat.Prime 167 := by norm_num
private theorem prime_fortyOneAM_173 : Nat.Prime 173 := by norm_num
private theorem prime_fortyOneAM_179 : Nat.Prime 179 := by norm_num
private theorem prime_fortyOneAM_181 : Nat.Prime 181 := by norm_num
private theorem prime_fortyOneAM_191 : Nat.Prime 191 := by norm_num
private theorem prime_fortyOneAM_193 : Nat.Prime 193 := by norm_num
private theorem prime_fortyOneAM_199 : Nat.Prime 199 := by norm_num
private theorem prime_fortyOneAM_211 : Nat.Prime 211 := by norm_num
private theorem prime_fortyOneAM_223 : Nat.Prime 223 := by norm_num
private theorem prime_fortyOneAM_227 : Nat.Prime 227 := by norm_num
private theorem prime_fortyOneAM_229 : Nat.Prime 229 := by norm_num
private theorem prime_fortyOneAM_233 : Nat.Prime 233 := by norm_num
private theorem prime_fortyOneAM_239 : Nat.Prime 239 := by norm_num
private theorem prime_fortyOneAM_241 : Nat.Prime 241 := by norm_num
private theorem prime_fortyOneAM_251 : Nat.Prime 251 := by norm_num
private theorem prime_fortyOneAM_269 : Nat.Prime 269 := by norm_num
private theorem prime_fortyOneAM_271 : Nat.Prime 271 := by norm_num
private theorem prime_fortyOneAM_277 : Nat.Prime 277 := by norm_num
private theorem prime_fortyOneAM_307 : Nat.Prime 307 := by norm_num
private theorem prime_fortyOneAM_313 : Nat.Prime 313 := by norm_num
private theorem prime_fortyOneAM_337 : Nat.Prime 337 := by norm_num
private theorem prime_fortyOneAM_347 : Nat.Prime 347 := by norm_num
private theorem prime_fortyOneAM_349 : Nat.Prime 349 := by norm_num
private theorem prime_fortyOneAM_353 : Nat.Prime 353 := by norm_num
private theorem prime_fortyOneAM_359 : Nat.Prime 359 := by norm_num
private theorem prime_fortyOneAM_367 : Nat.Prime 367 := by norm_num
private theorem prime_fortyOneAM_373 : Nat.Prime 373 := by norm_num
private theorem prime_fortyOneAM_379 : Nat.Prime 379 := by norm_num
private theorem prime_fortyOneAM_383 : Nat.Prime 383 := by norm_num
private theorem prime_fortyOneAM_397 : Nat.Prime 397 := by norm_num
private theorem prime_fortyOneAM_409 : Nat.Prime 409 := by norm_num
private theorem prime_fortyOneAM_433 : Nat.Prime 433 := by norm_num
private theorem prime_fortyOneAM_443 : Nat.Prime 443 := by norm_num
private theorem prime_fortyOneAM_463 : Nat.Prime 463 := by norm_num
private theorem prime_fortyOneAM_467 : Nat.Prime 467 := by norm_num
private theorem prime_fortyOneAM_491 : Nat.Prime 491 := by norm_num
private theorem prime_fortyOneAM_509 : Nat.Prime 509 := by norm_num
private theorem prime_fortyOneAM_521 : Nat.Prime 521 := by norm_num
private theorem prime_fortyOneAM_541 : Nat.Prime 541 := by norm_num
private theorem prime_fortyOneAM_547 : Nat.Prime 547 := by norm_num
private theorem prime_fortyOneAM_571 : Nat.Prime 571 := by norm_num
private theorem prime_fortyOneAM_577 : Nat.Prime 577 := by norm_num
private theorem prime_fortyOneAM_599 : Nat.Prime 599 := by norm_num
private theorem prime_fortyOneAM_601 : Nat.Prime 601 := by norm_num
private theorem prime_fortyOneAM_631 : Nat.Prime 631 := by norm_num
private theorem prime_fortyOneAM_643 : Nat.Prime 643 := by norm_num
private theorem prime_fortyOneAM_653 : Nat.Prime 653 := by norm_num
private theorem prime_fortyOneAM_661 : Nat.Prime 661 := by norm_num
private theorem prime_fortyOneAM_673 : Nat.Prime 673 := by norm_num
private theorem prime_fortyOneAM_677 : Nat.Prime 677 := by norm_num
private theorem prime_fortyOneAM_683 : Nat.Prime 683 := by norm_num
private theorem prime_fortyOneAM_733 : Nat.Prime 733 := by norm_num
private theorem prime_fortyOneAM_739 : Nat.Prime 739 := by norm_num
private theorem prime_fortyOneAM_769 : Nat.Prime 769 := by norm_num
private theorem prime_fortyOneAM_827 : Nat.Prime 827 := by norm_num
private theorem prime_fortyOneAM_839 : Nat.Prime 839 := by norm_num
private theorem prime_fortyOneAM_859 : Nat.Prime 859 := by norm_num
private theorem prime_fortyOneAM_877 : Nat.Prime 877 := by norm_num
private theorem prime_fortyOneAM_883 : Nat.Prime 883 := by norm_num
private theorem prime_fortyOneAM_887 : Nat.Prime 887 := by norm_num
private theorem prime_fortyOneAM_911 : Nat.Prime 911 := by norm_num
private theorem prime_fortyOneAM_937 : Nat.Prime 937 := by norm_num
private theorem prime_fortyOneAM_941 : Nat.Prime 941 := by norm_num
private theorem prime_fortyOneAM_977 : Nat.Prime 977 := by norm_num
private theorem prime_fortyOneAM_991 : Nat.Prime 991 := by norm_num
private theorem prime_fortyOneAM_997 : Nat.Prime 997 := by norm_num
private theorem prime_fortyOneAM_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_fortyOneAM_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_fortyOneAM_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_fortyOneAM_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_fortyOneAM_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_fortyOneAM_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_fortyOneAM_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_fortyOneAM_1129 : Nat.Prime 1129 := by norm_num
private theorem prime_fortyOneAM_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_fortyOneAM_1237 : Nat.Prime 1237 := by norm_num
private theorem prime_fortyOneAM_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_fortyOneAM_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_fortyOneAM_1289 : Nat.Prime 1289 := by norm_num
private theorem prime_fortyOneAM_1301 : Nat.Prime 1301 := by norm_num
private theorem prime_fortyOneAM_1409 : Nat.Prime 1409 := by norm_num
private theorem prime_fortyOneAM_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_fortyOneAM_1489 : Nat.Prime 1489 := by norm_num
private theorem prime_fortyOneAM_1583 : Nat.Prime 1583 := by norm_num
private theorem prime_fortyOneAM_1597 : Nat.Prime 1597 := by norm_num
private theorem prime_fortyOneAM_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_fortyOneAM_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_fortyOneAM_1847 : Nat.Prime 1847 := by norm_num
private theorem prime_fortyOneAM_1999 : Nat.Prime 1999 := by norm_num
private theorem prime_fortyOneAM_2069 : Nat.Prime 2069 := by norm_num
private theorem prime_fortyOneAM_2083 : Nat.Prime 2083 := by norm_num
private theorem prime_fortyOneAM_2087 : Nat.Prime 2087 := by norm_num
private theorem prime_fortyOneAM_2089 : Nat.Prime 2089 := by norm_num
private theorem prime_fortyOneAM_2137 : Nat.Prime 2137 := by norm_num
private theorem prime_fortyOneAM_2153 : Nat.Prime 2153 := by norm_num
private theorem prime_fortyOneAM_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_fortyOneAM_2393 : Nat.Prime 2393 := by norm_num
private theorem prime_fortyOneAM_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_fortyOneAM_2657 : Nat.Prime 2657 := by norm_num
private theorem prime_fortyOneAM_2671 : Nat.Prime 2671 := by norm_num
private theorem prime_fortyOneAM_2689 : Nat.Prime 2689 := by norm_num
private theorem prime_fortyOneAM_2719 : Nat.Prime 2719 := by norm_num
private theorem prime_fortyOneAM_2897 : Nat.Prime 2897 := by norm_num
private theorem prime_fortyOneAM_2917 : Nat.Prime 2917 := by norm_num
private theorem prime_fortyOneAM_2963 : Nat.Prime 2963 := by norm_num
private theorem prime_fortyOneAM_3023 : Nat.Prime 3023 := by norm_num
private theorem prime_fortyOneAM_3449 : Nat.Prime 3449 := by norm_num
private theorem prime_fortyOneAM_3457 : Nat.Prime 3457 := by norm_num
private theorem prime_fortyOneAM_3547 : Nat.Prime 3547 := by norm_num
private theorem prime_fortyOneAM_3583 : Nat.Prime 3583 := by norm_num
private theorem prime_fortyOneAM_3673 : Nat.Prime 3673 := by norm_num
private theorem prime_fortyOneAM_3727 : Nat.Prime 3727 := by norm_num
private theorem prime_fortyOneAM_3767 : Nat.Prime 3767 := by norm_num
private theorem prime_fortyOneAM_3989 : Nat.Prime 3989 := by norm_num
private theorem prime_fortyOneAM_4049 : Nat.Prime 4049 := by norm_num
private theorem prime_fortyOneAM_4051 : Nat.Prime 4051 := by norm_num
private theorem prime_fortyOneAM_4153 : Nat.Prime 4153 := by norm_num
private theorem prime_fortyOneAM_4211 : Nat.Prime 4211 := by norm_num
private theorem prime_fortyOneAM_4217 : Nat.Prime 4217 := by norm_num
private theorem prime_fortyOneAM_4289 : Nat.Prime 4289 := by norm_num
private theorem prime_fortyOneAM_4391 : Nat.Prime 4391 := by norm_num
private theorem prime_fortyOneAM_4483 : Nat.Prime 4483 := by norm_num
private theorem prime_fortyOneAM_4783 : Nat.Prime 4783 := by norm_num
private theorem prime_fortyOneAM_4793 : Nat.Prime 4793 := by norm_num
private theorem prime_fortyOneAM_4937 : Nat.Prime 4937 := by norm_num
private theorem prime_fortyOneAM_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fortyOneAM_5081 : Nat.Prime 5081 := by norm_num
private theorem prime_fortyOneAM_5381 : Nat.Prime 5381 := by norm_num
private theorem prime_fortyOneAM_5471 : Nat.Prime 5471 := by norm_num
private theorem prime_fortyOneAM_5813 : Nat.Prime 5813 := by norm_num
private theorem prime_fortyOneAM_6709 : Nat.Prime 6709 := by norm_num
private theorem prime_fortyOneAM_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_fortyOneAM_6961 : Nat.Prime 6961 := by norm_num
private theorem prime_fortyOneAM_7043 : Nat.Prime 7043 := by norm_num
private theorem prime_fortyOneAM_7057 : Nat.Prime 7057 := by norm_num
private theorem prime_fortyOneAM_7177 : Nat.Prime 7177 := by norm_num
private theorem prime_fortyOneAM_7451 : Nat.Prime 7451 := by norm_num
private theorem prime_fortyOneAM_7603 : Nat.Prime 7603 := by norm_num
private theorem prime_fortyOneAM_7621 : Nat.Prime 7621 := by norm_num
private theorem prime_fortyOneAM_7793 : Nat.Prime 7793 := by norm_num
private theorem prime_fortyOneAM_7817 : Nat.Prime 7817 := by norm_num
private theorem prime_fortyOneAM_8081 : Nat.Prime 8081 := by norm_num
private theorem prime_fortyOneAM_8161 : Nat.Prime 8161 := by norm_num
private theorem prime_fortyOneAM_8317 : Nat.Prime 8317 := by norm_num
private theorem prime_fortyOneAM_8447 : Nat.Prime 8447 := by norm_num
private theorem prime_fortyOneAM_8501 : Nat.Prime 8501 := by norm_num
private theorem prime_fortyOneAM_9293 : Nat.Prime 9293 := by norm_num
private theorem prime_fortyOneAM_9377 : Nat.Prime 9377 := by norm_num
private theorem prime_fortyOneAM_9403 : Nat.Prime 9403 := by norm_num
private theorem prime_fortyOneAM_9547 : Nat.Prime 9547 := by norm_num
private theorem prime_fortyOneAM_10099 : Nat.Prime 10099 := by norm_num
private theorem prime_fortyOneAM_10159 : Nat.Prime 10159 := by norm_num
private theorem prime_fortyOneAM_10589 : Nat.Prime 10589 := by norm_num
private theorem prime_fortyOneAM_10781 : Nat.Prime 10781 := by norm_num
private theorem prime_fortyOneAM_10799 : Nat.Prime 10799 := by norm_num
private theorem prime_fortyOneAM_10847 : Nat.Prime 10847 := by norm_num
private theorem prime_fortyOneAM_11681 : Nat.Prime 11681 := by norm_num
private theorem prime_fortyOneAM_11789 : Nat.Prime 11789 := by norm_num
private theorem prime_fortyOneAM_11867 : Nat.Prime 11867 := by norm_num
private theorem prime_fortyOneAM_12503 : Nat.Prime 12503 := by norm_num
private theorem prime_fortyOneAM_12653 : Nat.Prime 12653 := by norm_num
private theorem prime_fortyOneAM_13469 : Nat.Prime 13469 := by norm_num
private theorem prime_fortyOneAM_13619 : Nat.Prime 13619 := by norm_num
private theorem prime_fortyOneAM_15121 : Nat.Prime 15121 := by norm_num
private theorem prime_fortyOneAM_15269 : Nat.Prime 15269 := by norm_num
private theorem prime_fortyOneAM_16189 : Nat.Prime 16189 := by norm_num
private theorem prime_fortyOneAM_16411 : Nat.Prime 16411 := by norm_num
private theorem prime_fortyOneAM_16631 : Nat.Prime 16631 := by norm_num
private theorem prime_fortyOneAM_16759 : Nat.Prime 16759 := by norm_num
private theorem prime_fortyOneAM_17137 : Nat.Prime 17137 := by norm_num
private theorem prime_fortyOneAM_17291 : Nat.Prime 17291 := by norm_num
private theorem prime_fortyOneAM_18457 : Nat.Prime 18457 := by norm_num
private theorem prime_fortyOneAM_19391 : Nat.Prime 19391 := by norm_num
private theorem prime_fortyOneAM_19661 : Nat.Prime 19661 := by norm_num
private theorem prime_fortyOneAM_19991 : Nat.Prime 19991 := by norm_num
private theorem prime_fortyOneAM_22171 : Nat.Prime 22171 := by norm_num
private theorem prime_fortyOneAM_22621 : Nat.Prime 22621 := by norm_num
private theorem prime_fortyOneAM_22777 : Nat.Prime 22777 := by norm_num
private theorem prime_fortyOneAM_22973 : Nat.Prime 22973 := by norm_num
private theorem prime_fortyOneAM_23767 : Nat.Prime 23767 := by norm_num
private theorem prime_fortyOneAM_24109 : Nat.Prime 24109 := by norm_num
private theorem prime_fortyOneAM_25321 : Nat.Prime 25321 := by norm_num
private theorem prime_fortyOneAM_25841 : Nat.Prime 25841 := by norm_num
private theorem prime_fortyOneAM_26729 : Nat.Prime 26729 := by norm_num
private theorem prime_fortyOneAM_28031 : Nat.Prime 28031 := by norm_num
private theorem prime_fortyOneAM_28351 : Nat.Prime 28351 := by norm_num
private theorem prime_fortyOneAM_29153 : Nat.Prime 29153 := by norm_num
private theorem prime_fortyOneAM_29339 : Nat.Prime 29339 := by norm_num
private theorem prime_fortyOneAM_29867 : Nat.Prime 29867 := by norm_num
private theorem prime_fortyOneAM_30509 : Nat.Prime 30509 := by norm_num
private theorem prime_fortyOneAM_32237 : Nat.Prime 32237 := by norm_num
private theorem prime_fortyOneAM_32653 : Nat.Prime 32653 := by norm_num
private theorem prime_fortyOneAM_32713 : Nat.Prime 32713 := by norm_num
private theorem prime_fortyOneAM_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_fortyOneAM_35747 : Nat.Prime 35747 := by norm_num
private theorem prime_fortyOneAM_36107 : Nat.Prime 36107 := by norm_num
private theorem prime_fortyOneAM_36871 : Nat.Prime 36871 := by norm_num
private theorem prime_fortyOneAM_37199 : Nat.Prime 37199 := by norm_num
private theorem prime_fortyOneAM_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_fortyOneAM_38149 : Nat.Prime 38149 := by norm_num
private theorem prime_fortyOneAM_38183 : Nat.Prime 38183 := by norm_num
private theorem prime_fortyOneAM_39443 : Nat.Prime 39443 := by norm_num
private theorem prime_fortyOneAM_43291 : Nat.Prime 43291 := by norm_num
private theorem prime_fortyOneAM_47933 : Nat.Prime 47933 := by norm_num
private theorem prime_fortyOneAM_48679 : Nat.Prime 48679 := by norm_num
private theorem prime_fortyOneAM_51803 : Nat.Prime 51803 := by norm_num
private theorem prime_fortyOneAM_54851 : Nat.Prime 54851 := by norm_num
private theorem prime_fortyOneAM_56209 : Nat.Prime 56209 := by norm_num
private theorem prime_fortyOneAM_56983 : Nat.Prime 56983 := by norm_num
private theorem prime_fortyOneAM_57527 : Nat.Prime 57527 := by norm_num
private theorem prime_fortyOneAM_59443 : Nat.Prime 59443 := by norm_num
private theorem prime_fortyOneAM_60887 : Nat.Prime 60887 := by norm_num
private theorem prime_fortyOneAM_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_fortyOneAM_63727 : Nat.Prime 63727 := by norm_num
private theorem prime_fortyOneAM_64969 : Nat.Prime 64969 := by norm_num
private theorem prime_fortyOneAM_65881 : Nat.Prime 65881 := by norm_num
private theorem prime_fortyOneAM_71237 : Nat.Prime 71237 := by norm_num
private theorem prime_fortyOneAM_81203 : Nat.Prime 81203 := by norm_num
private theorem prime_fortyOneAM_81853 : Nat.Prime 81853 := by norm_num
private theorem prime_fortyOneAM_88261 : Nat.Prime 88261 := by norm_num
private theorem prime_fortyOneAM_92737 : Nat.Prime 92737 := by norm_num
private theorem prime_fortyOneAM_98129 : Nat.Prime 98129 := by norm_num
private theorem prime_fortyOneAM_98737 : Nat.Prime 98737 := by norm_num
private theorem prime_fortyOneAM_101341 : Nat.Prime 101341 := by norm_num
private theorem prime_fortyOneAM_101533 : Nat.Prime 101533 := by norm_num
private theorem prime_fortyOneAM_106321 : Nat.Prime 106321 := by norm_num
private theorem prime_fortyOneAM_109831 : Nat.Prime 109831 := by norm_num
private theorem prime_fortyOneAM_124133 : Nat.Prime 124133 := by norm_num
private theorem prime_fortyOneAM_127399 : Nat.Prime 127399 := by norm_num
private theorem prime_fortyOneAM_133717 : Nat.Prime 133717 := by norm_num
private theorem prime_fortyOneAM_149627 : Nat.Prime 149627 := by norm_num
private theorem prime_fortyOneAM_150889 : Nat.Prime 150889 := by norm_num
private theorem prime_fortyOneAM_151279 : Nat.Prime 151279 := by norm_num
private theorem prime_fortyOneAM_156671 : Nat.Prime 156671 := by norm_num
private theorem prime_fortyOneAM_157999 : Nat.Prime 157999 := by norm_num
private theorem prime_fortyOneAM_158419 : Nat.Prime 158419 := by norm_num
private theorem prime_fortyOneAM_159631 : Nat.Prime 159631 := by norm_num
private theorem prime_fortyOneAM_161267 : Nat.Prime 161267 := by norm_num
private theorem prime_fortyOneAM_166867 : Nat.Prime 166867 := by norm_num
private theorem prime_fortyOneAM_166949 : Nat.Prime 166949 := by norm_num
private theorem prime_fortyOneAM_174157 : Nat.Prime 174157 := by norm_num
private theorem prime_fortyOneAM_180749 : Nat.Prime 180749 := by norm_num
private theorem prime_fortyOneAM_185089 : Nat.Prime 185089 := by norm_num
private theorem prime_fortyOneAM_193577 : Nat.Prime 193577 := by norm_num
private theorem prime_fortyOneAM_198929 : Nat.Prime 198929 := by norm_num
private theorem prime_fortyOneAM_203351 : Nat.Prime 203351 := by norm_num
private theorem prime_fortyOneAM_204007 : Nat.Prime 204007 := by norm_num
private theorem prime_fortyOneAM_206477 : Nat.Prime 206477 := by norm_num
private theorem prime_fortyOneAM_210709 : Nat.Prime 210709 := by norm_num
private theorem prime_fortyOneAM_228611 : Nat.Prime 228611 := by norm_num
private theorem prime_fortyOneAM_241337 : Nat.Prime 241337 := by norm_num
private theorem prime_fortyOneAM_241781 : Nat.Prime 241781 := by norm_num
private theorem prime_fortyOneAM_261581 : Nat.Prime 261581 := by norm_num
private theorem prime_fortyOneAM_262111 : Nat.Prime 262111 := by norm_num
private theorem prime_fortyOneAM_272299 : Nat.Prime 272299 := by norm_num
private theorem prime_fortyOneAM_278581 : Nat.Prime 278581 := by norm_num
private theorem prime_fortyOneAM_283813 : Nat.Prime 283813 := by norm_num
private theorem prime_fortyOneAM_296509 : Nat.Prime 296509 := by norm_num
private theorem prime_fortyOneAM_304897 : Nat.Prime 304897 := by norm_num
private theorem prime_fortyOneAM_309521 : Nat.Prime 309521 := by norm_num
private theorem prime_fortyOneAM_312563 : Nat.Prime 312563 := by norm_num
private theorem prime_fortyOneAM_317453 : Nat.Prime 317453 := by norm_num
private theorem prime_fortyOneAM_318569 : Nat.Prime 318569 := by norm_num
private theorem prime_fortyOneAM_325813 : Nat.Prime 325813 := by norm_num
private theorem prime_fortyOneAM_331339 : Nat.Prime 331339 := by norm_num
private theorem prime_fortyOneAM_336599 : Nat.Prime 336599 := by norm_num
private theorem prime_fortyOneAM_358349 : Nat.Prime 358349 := by norm_num
private theorem prime_fortyOneAM_374111 : Nat.Prime 374111 := by norm_num
private theorem prime_fortyOneAM_375901 : Nat.Prime 375901 := by norm_num
private theorem prime_fortyOneAM_394453 : Nat.Prime 394453 := by norm_num
private theorem prime_fortyOneAM_396259 : Nat.Prime 396259 := by norm_num
private theorem prime_fortyOneAM_422057 : Nat.Prime 422057 := by norm_num
private theorem prime_fortyOneAM_430979 : Nat.Prime 430979 := by norm_num
private theorem prime_fortyOneAM_435109 : Nat.Prime 435109 := by norm_num
private theorem prime_fortyOneAM_476243 : Nat.Prime 476243 := by norm_num
private theorem prime_fortyOneAM_478411 : Nat.Prime 478411 := by norm_num
private theorem prime_fortyOneAM_509659 : Nat.Prime 509659 := by norm_num
private theorem prime_fortyOneAM_513943 : Nat.Prime 513943 := by norm_num
private theorem prime_fortyOneAM_543689 : Nat.Prime 543689 := by norm_num
private theorem prime_fortyOneAM_570601 : Nat.Prime 570601 := by norm_num
private theorem prime_fortyOneAM_633079 : Nat.Prime 633079 := by norm_num
private theorem prime_fortyOneAM_703393 : Nat.Prime 703393 := by norm_num
private theorem prime_fortyOneAM_759947 : Nat.Prime 759947 := by norm_num
private theorem prime_fortyOneAM_777097 : Nat.Prime 777097 := by norm_num
private theorem prime_fortyOneAM_785431 : Nat.Prime 785431 := by norm_num
private theorem prime_fortyOneAM_789709 : Nat.Prime 789709 := by norm_num
private theorem prime_fortyOneAM_883093 : Nat.Prime 883093 := by norm_num
private theorem prime_fortyOneAM_917227 : Nat.Prime 917227 := by norm_num
private theorem prime_fortyOneAM_957091 : Nat.Prime 957091 := by norm_num
private theorem prime_fortyOneAM_999763 : Nat.Prime 999763 := by norm_num
private theorem prime_fortyOneAM_1005241 : Nat.Prime 1005241 := by norm_num
private theorem prime_fortyOneAM_1011289 : Nat.Prime 1011289 := by norm_num
private theorem prime_fortyOneAM_1081723 : Nat.Prime 1081723 := by norm_num
private theorem prime_fortyOneAM_1111211 : Nat.Prime 1111211 := by norm_num
private theorem prime_fortyOneAM_1225883 : Nat.Prime 1225883 := by norm_num
private theorem prime_fortyOneAM_1231873 : Nat.Prime 1231873 := by norm_num
private theorem prime_fortyOneAM_1243741 : Nat.Prime 1243741 := by norm_num
private theorem prime_fortyOneAM_1277249 : Nat.Prime 1277249 := by norm_num
private theorem prime_fortyOneAM_1307101 : Nat.Prime 1307101 := by norm_num
private theorem prime_fortyOneAM_1308499 : Nat.Prime 1308499 := by norm_num
private theorem prime_fortyOneAM_1335749 : Nat.Prime 1335749 := by norm_num
private theorem prime_fortyOneAM_1362367 : Nat.Prime 1362367 := by norm_num
private theorem prime_fortyOneAM_1394857 : Nat.Prime 1394857 := by norm_num
private theorem prime_fortyOneAM_1583447 : Nat.Prime 1583447 := by norm_num
private theorem prime_fortyOneAM_1586773 : Nat.Prime 1586773 := by norm_num
private theorem prime_fortyOneAM_1619903 : Nat.Prime 1619903 := by norm_num
private theorem prime_fortyOneAM_1668521 : Nat.Prime 1668521 := by norm_num
private theorem prime_fortyOneAM_1679261 : Nat.Prime 1679261 := by norm_num
private theorem prime_fortyOneAM_1939523 : Nat.Prime 1939523 := by norm_num
private theorem prime_fortyOneAM_1971553 : Nat.Prime 1971553 := by norm_num
private theorem prime_fortyOneAM_2080439 : Nat.Prime 2080439 := by norm_num
private theorem prime_fortyOneAM_2250713 : Nat.Prime 2250713 := by norm_num
private theorem prime_fortyOneAM_2266133 : Nat.Prime 2266133 := by norm_num
private theorem prime_fortyOneAM_2369183 : Nat.Prime 2369183 := by norm_num
private theorem prime_fortyOneAM_2543441 : Nat.Prime 2543441 := by norm_num
private theorem prime_fortyOneAM_2690803 : Nat.Prime 2690803 := by norm_num
private theorem prime_fortyOneAM_2781817 : Nat.Prime 2781817 := by norm_num
private theorem prime_fortyOneAM_2830489 : Nat.Prime 2830489 := by norm_num
private theorem prime_fortyOneAM_2945807 : Nat.Prime 2945807 := by norm_num
private theorem prime_fortyOneAM_2983363 : Nat.Prime 2983363 := by norm_num
private theorem prime_fortyOneAM_3178631 : Nat.Prime 3178631 := by norm_num
private theorem prime_fortyOneAM_3229189 : Nat.Prime 3229189 := by norm_num
private theorem prime_fortyOneAM_3413789 : Nat.Prime 3413789 := by norm_num
private theorem prime_fortyOneAM_3636667 : Nat.Prime 3636667 := by norm_num
private theorem prime_fortyOneAM_4160357 : Nat.Prime 4160357 := by norm_num
private theorem prime_fortyOneAM_4255313 : Nat.Prime 4255313 := by norm_num
private theorem prime_fortyOneAM_4463489 : Nat.Prime 4463489 := by norm_num
private theorem prime_fortyOneAM_4619123 : Nat.Prime 4619123 := by norm_num
private theorem prime_fortyOneAM_5164591 : Nat.Prime 5164591 := by norm_num
private theorem prime_fortyOneAM_5311589 : Nat.Prime 5311589 := by norm_num
private theorem prime_fortyOneAM_5423179 : Nat.Prime 5423179 := by norm_num
private theorem prime_fortyOneAM_5747849 : Nat.Prime 5747849 := by norm_num
private theorem prime_fortyOneAM_5876993 : Nat.Prime 5876993 := by norm_num
private theorem prime_fortyOneAM_6010489 : Nat.Prime 6010489 := by norm_num
private theorem prime_fortyOneAM_6105223 : Nat.Prime 6105223 := by norm_num
private theorem prime_fortyOneAM_6186967 : Nat.Prime 6186967 := by norm_num
private theorem prime_fortyOneAM_6408799 : Nat.Prime 6408799 := by norm_num
private theorem prime_fortyOneAM_6600031 : Nat.Prime 6600031 := by norm_num
private theorem prime_fortyOneAM_6698767 : Nat.Prime 6698767 := by norm_num
private theorem prime_fortyOneAM_6707161 : Nat.Prime 6707161 := by norm_num
private theorem prime_fortyOneAM_7087357 : Nat.Prime 7087357 := by norm_num
private theorem prime_fortyOneAM_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_fortyOneAM_7306129 : Nat.Prime 7306129 := by norm_num
private theorem prime_fortyOneAM_7954799 : Nat.Prime 7954799 := by norm_num
private theorem prime_fortyOneAM_7981327 : Nat.Prime 7981327 := by norm_num
private theorem prime_fortyOneAM_8348551 : Nat.Prime 8348551 := by norm_num
private theorem prime_fortyOneAM_9056737 : Nat.Prime 9056737 := by norm_num
private theorem prime_fortyOneAM_9652759 : Nat.Prime 9652759 := by norm_num
private theorem prime_fortyOneAM_9847969 : Nat.Prime 9847969 := by norm_num
private theorem prime_fortyOneAM_10339531 : Nat.Prime 10339531 := by norm_num
private theorem prime_fortyOneAM_10400987 : Nat.Prime 10400987 := by norm_num
private theorem prime_fortyOneAM_10600679 : Nat.Prime 10600679 := by norm_num
private theorem prime_fortyOneAM_10976507 : Nat.Prime 10976507 := by norm_num
private theorem prime_fortyOneAM_12003457 : Nat.Prime 12003457 := by norm_num
private theorem prime_fortyOneAM_12286249 : Nat.Prime 12286249 := by norm_num
private theorem prime_fortyOneAM_12445397 : Nat.Prime 12445397 := by norm_num
private theorem prime_fortyOneAM_13249487 : Nat.Prime 13249487 := by norm_num
private theorem prime_fortyOneAM_14243681 : Nat.Prime 14243681 := by norm_num
private theorem prime_fortyOneAM_15565127 : Nat.Prime 15565127 := by norm_num
private theorem prime_fortyOneAM_18060617 : Nat.Prime 18060617 := by norm_num
private theorem prime_fortyOneAM_19218697 : Nat.Prime 19218697 := by norm_num
private theorem prime_fortyOneAM_19450429 : Nat.Prime 19450429 := by norm_num
private theorem prime_fortyOneAM_20878961 : Nat.Prime 20878961 := by norm_num
private theorem prime_fortyOneAM_21328451 : Nat.Prime 21328451 := by norm_num
private theorem prime_fortyOneAM_24774623 : Nat.Prime 24774623 := by norm_num
private theorem prime_fortyOneAM_29307587 : Nat.Prime 29307587 := by norm_num

private theorem prime_fortyOneAM_30524497 : Nat.Prime 30524497 := by
  apply lucas_primality 30524497 (5 : ZMod 30524497)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (43, 1), (643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (43, 1), (643, 1)] : List FactorBlock).map factorBlockValue).prod) = 30524497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_43
      · exact prime_fortyOneAM_643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 30524497) ^ 15262248 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 30524497) ^ 10174832 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 30524497) ^ 1327152 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 30524497) ^ 709872 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 30524497) ^ 47472 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_31004833 : Nat.Prime 31004833 := by
  apply lucas_primality 31004833 (5 : ZMod 31004833)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (109, 1), (2963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (109, 1), (2963, 1)] : List FactorBlock).map factorBlockValue).prod) = 31004833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_109
      · exact prime_fortyOneAM_2963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 31004833) ^ 15502416 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 31004833) ^ 10334944 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 31004833) ^ 284448 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 31004833) ^ 10464 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_31421581 : Nat.Prime 31421581 := by
  apply lucas_primality 31421581 (10 : ZMod 31421581)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (41, 1), (53, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (41, 1), (53, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) = 31421581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_41
      · exact prime_fortyOneAM_53
      · exact prime_fortyOneAM_241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 31421581) ^ 15710790 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 31421581) ^ 10473860 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 31421581) ^ 6284316 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 31421581) ^ 766380 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 31421581) ^ 592860 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 31421581) ^ 130380 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_33687119 : Nat.Prime 33687119 := by
  apply lucas_primality 33687119 (7 : ZMod 33687119)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (199, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (199, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) = 33687119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_53
      · exact prime_fortyOneAM_199
      · exact prime_fortyOneAM_1597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 33687119) ^ 16843559 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 33687119) ^ 635606 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 33687119) ^ 169282 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 33687119) ^ 21094 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_35261959 : Nat.Prime 35261959 := by
  apply lucas_primality 35261959 (3 : ZMod 35261959)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5876993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5876993, 1)] : List FactorBlock).map factorBlockValue).prod) = 35261959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5876993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 35261959) ^ 17630979 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35261959) ^ 11753986 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35261959) ^ 6 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_38708441 : Nat.Prime 38708441 := by
  apply lucas_primality 38708441 (6 : ZMod 38708441)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (239, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (239, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) = 38708441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_239
      · exact prime_fortyOneAM_4049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 38708441) ^ 19354220 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 38708441) ^ 7741688 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 38708441) ^ 161960 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 38708441) ^ 9560 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_41608781 : Nat.Prime 41608781 := by
  apply lucas_primality 41608781 (2 : ZMod 41608781)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2080439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2080439, 1)] : List FactorBlock).map factorBlockValue).prod) = 41608781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_2080439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41608781) ^ 20804390 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 41608781) ^ 8321756 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 41608781) ^ 20 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_41757923 : Nat.Prime 41757923 := by
  apply lucas_primality 41757923 (2 : ZMod 41757923)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20878961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20878961, 1)] : List FactorBlock).map factorBlockValue).prod) = 41757923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_20878961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 41757923) ^ 20878961 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 41757923) ^ 2 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_47488843 : Nat.Prime 47488843 := by
  apply lucas_primality 47488843 (3 : ZMod 47488843)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (433, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (433, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 47488843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_433
      · exact prime_fortyOneAM_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 47488843) ^ 23744421 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 47488843) ^ 15829614 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 47488843) ^ 109674 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 47488843) ^ 70146 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_47737639 : Nat.Prime 47737639 := by
  apply lucas_primality 47737639 (6 : ZMod 47737639)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (204007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (204007, 1)] : List FactorBlock).map factorBlockValue).prod) = 47737639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_204007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 47737639) ^ 23868819 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 47737639) ^ 15912546 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 47737639) ^ 3672126 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 47737639) ^ 234 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_48573649 : Nat.Prime 48573649 := by
  apply lucas_primality 48573649 (7 : ZMod 48573649)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (229, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (229, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 48573649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_229
      · exact prime_fortyOneAM_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 48573649) ^ 24286824 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 48573649) ^ 16191216 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 48573649) ^ 212112 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 48573649) ^ 98928 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_48745223 : Nat.Prime 48745223 := by
  apply lucas_primality 48745223 (5 : ZMod 48745223)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 1), (61, 1), (1237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 1), (61, 1), (1237, 1)] : List FactorBlock).map factorBlockValue).prod) = 48745223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_61
      · exact prime_fortyOneAM_1237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 48745223) ^ 24372611 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 48745223) ^ 2867366 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 48745223) ^ 2565538 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 48745223) ^ 799102 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 48745223) ^ 39406 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_55713781 : Nat.Prime 55713781 := by
  apply lucas_primality 55713781 (2 : ZMod 55713781)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (309521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (309521, 1)] : List FactorBlock).map factorBlockValue).prod) = 55713781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_309521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55713781) ^ 27856890 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 55713781) ^ 18571260 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 55713781) ^ 11142756 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 55713781) ^ 180 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_64512521 : Nat.Prime 64512521 := by
  apply lucas_primality 64512521 (6 : ZMod 64512521)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (383, 1), (4211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (383, 1), (4211, 1)] : List FactorBlock).map factorBlockValue).prod) = 64512521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_383
      · exact prime_fortyOneAM_4211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 64512521) ^ 32256260 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 64512521) ^ 12902504 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 64512521) ^ 168440 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 64512521) ^ 15320 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_67374239 : Nat.Prime 67374239 := by
  apply lucas_primality 67374239 (7 : ZMod 67374239)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (33687119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (33687119, 1)] : List FactorBlock).map factorBlockValue).prod) = 67374239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_33687119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 67374239) ^ 33687119 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 67374239) ^ 2 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_70873571 : Nat.Prime 70873571 := by
  apply lucas_primality 70873571 (2 : ZMod 70873571)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7087357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7087357, 1)] : List FactorBlock).map factorBlockValue).prod) = 70873571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7087357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 70873571) ^ 35436785 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 70873571) ^ 14174714 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 70873571) ^ 10 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_73129513 : Nat.Prime 73129513 := by
  apply lucas_primality 73129513 (5 : ZMod 73129513)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (23, 1), (7793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (23, 1), (7793, 1)] : List FactorBlock).map factorBlockValue).prod) = 73129513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_7793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 73129513) ^ 36564756 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 73129513) ^ 24376504 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 73129513) ^ 4301736 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 73129513) ^ 3179544 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 73129513) ^ 9384 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_73754173 : Nat.Prime 73754173 := by
  apply lucas_primality 73754173 (5 : ZMod 73754173)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (37, 1), (18457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (37, 1), (18457, 1)] : List FactorBlock).map factorBlockValue).prod) = 73754173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_37
      · exact prime_fortyOneAM_18457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 73754173) ^ 36877086 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 73754173) ^ 24584724 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 73754173) ^ 1993356 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 73754173) ^ 3996 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_74362247 : Nat.Prime 74362247 := by
  apply lucas_primality 74362247 (5 : ZMod 74362247)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (5311589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (5311589, 1)] : List FactorBlock).map factorBlockValue).prod) = 74362247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_5311589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 74362247) ^ 37181123 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 74362247) ^ 10623178 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 74362247) ^ 14 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_75153751 : Nat.Prime 75153751 := by
  apply lucas_primality 75153751 (3 : ZMod 75153751)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 4), (7, 2), (409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 4), (7, 2), (409, 1)] : List FactorBlock).map factorBlockValue).prod) = 75153751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 75153751) ^ 37576875 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 75153751) ^ 25051250 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 75153751) ^ 15030750 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 75153751) ^ 10736250 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 75153751) ^ 183750 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_76537907 : Nat.Prime 76537907 := by
  apply lucas_primality 76537907 (2 : ZMod 76537907)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3767, 1), (10159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3767, 1), (10159, 1)] : List FactorBlock).map factorBlockValue).prod) = 76537907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3767
      · exact prime_fortyOneAM_10159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 76537907) ^ 38268953 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 76537907) ^ 20318 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 76537907) ^ 7534 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_81955763 : Nat.Prime 81955763 := by
  apply lucas_primality 81955763 (2 : ZMod 81955763)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (199, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (199, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) = 81955763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_199
      · exact prime_fortyOneAM_1279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 81955763) ^ 40977881 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 81955763) ^ 11707966 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 81955763) ^ 3563294 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 81955763) ^ 411838 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 81955763) ^ 64078 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_97490447 : Nat.Prime 97490447 := by
  apply lucas_primality 97490447 (5 : ZMod 97490447)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (48745223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (48745223, 1)] : List FactorBlock).map factorBlockValue).prod) = 97490447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_48745223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 97490447) ^ 48745223 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 97490447) ^ 2 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_118685009 : Nat.Prime 118685009 := by
  apply lucas_primality 118685009 (3 : ZMod 118685009)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (570601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (570601, 1)] : List FactorBlock).map factorBlockValue).prod) = 118685009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_570601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 118685009) ^ 59342504 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 118685009) ^ 9129616 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 118685009) ^ 208 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_118880539 : Nat.Prime 118880539 := by
  apply lucas_primality 118880539 (2 : ZMod 118880539)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (2830489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (2830489, 1)] : List FactorBlock).map factorBlockValue).prod) = 118880539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_2830489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 118880539) ^ 59440269 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 118880539) ^ 39626846 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 118880539) ^ 16982934 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 118880539) ^ 42 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_119348533 : Nat.Prime 119348533 := by
  apply lucas_primality 119348533 (7 : ZMod 119348533)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (37, 1), (29867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (37, 1), (29867, 1)] : List FactorBlock).map factorBlockValue).prod) = 119348533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_37
      · exact prime_fortyOneAM_29867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 119348533) ^ 59674266 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 119348533) ^ 39782844 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 119348533) ^ 3225636 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 119348533) ^ 3996 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_126834817 : Nat.Prime 126834817 := by
  apply lucas_primality 126834817 (5 : ZMod 126834817)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (37, 1), (79, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (37, 1), (79, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) = 126834817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_37
      · exact prime_fortyOneAM_79
      · exact prime_fortyOneAM_113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 126834817) ^ 63417408 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 126834817) ^ 42278272 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 126834817) ^ 3427968 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 126834817) ^ 1605504 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 126834817) ^ 1122432 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_136460353 : Nat.Prime 136460353 := by
  apply lucas_primality 136460353 (5 : ZMod 136460353)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (101533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (101533, 1)] : List FactorBlock).map factorBlockValue).prod) = 136460353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_101533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 136460353) ^ 68230176 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 136460353) ^ 45486784 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 136460353) ^ 19494336 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 136460353) ^ 1344 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_146932391 : Nat.Prime 146932391 := by
  apply lucas_primality 146932391 (7 : ZMod 146932391)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (1335749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (1335749, 1)] : List FactorBlock).map factorBlockValue).prod) = 146932391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_1335749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 146932391) ^ 73466195 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 146932391) ^ 29386478 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 146932391) ^ 13357490 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 146932391) ^ 110 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_149772853 : Nat.Prime 149772853 := by
  apply lucas_primality 149772853 (2 : ZMod 149772853)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (4160357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (4160357, 1)] : List FactorBlock).map factorBlockValue).prod) = 149772853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_4160357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 149772853) ^ 74886426 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 149772853) ^ 49924284 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 149772853) ^ 36 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_162489113 : Nat.Prime 162489113 := by
  apply lucas_primality 162489113 (3 : ZMod 162489113)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (883093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (883093, 1)] : List FactorBlock).map factorBlockValue).prod) = 162489113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_883093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 162489113) ^ 81244556 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 162489113) ^ 7064744 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 162489113) ^ 184 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_178906369 : Nat.Prime 178906369 := by
  apply lucas_primality 178906369 (7 : ZMod 178906369)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (17, 1), (71, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (17, 1), (71, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) = 178906369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_71
      · exact prime_fortyOneAM_193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 178906369) ^ 89453184 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 178906369) ^ 59635456 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 178906369) ^ 10523904 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 178906369) ^ 2519808 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 178906369) ^ 926976 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_187955711 : Nat.Prime 187955711 := by
  apply lucas_primality 187955711 (11 : ZMod 187955711)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (59, 1), (318569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (59, 1), (318569, 1)] : List FactorBlock).map factorBlockValue).prod) = 187955711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_59
      · exact prime_fortyOneAM_318569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 187955711) ^ 93977855 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 187955711) ^ 37591142 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 187955711) ^ 3185690 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 187955711) ^ 590 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_194388361 : Nat.Prime 194388361 := by
  apply lucas_primality 194388361 (11 : ZMod 194388361)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (1619903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (1619903, 1)] : List FactorBlock).map factorBlockValue).prod) = 194388361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_1619903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 194388361) ^ 97194180 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 194388361) ^ 64796120 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 194388361) ^ 38877672 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 194388361) ^ 120 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_203570467 : Nat.Prime 203570467 := by
  apply lucas_primality 203570467 (3 : ZMod 203570467)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (229, 1), (13469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (229, 1), (13469, 1)] : List FactorBlock).map factorBlockValue).prod) = 203570467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_229
      · exact prime_fortyOneAM_13469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 203570467) ^ 101785233 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 203570467) ^ 67856822 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 203570467) ^ 18506406 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 203570467) ^ 888954 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 203570467) ^ 15114 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_203735881 : Nat.Prime 203735881 := by
  apply lucas_primality 203735881 (7 : ZMod 203735881)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (191, 1), (2963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (191, 1), (2963, 1)] : List FactorBlock).map factorBlockValue).prod) = 203735881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_191
      · exact prime_fortyOneAM_2963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 203735881) ^ 101867940 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 203735881) ^ 67911960 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 203735881) ^ 40747176 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 203735881) ^ 1066680 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 203735881) ^ 68760 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_206182633 : Nat.Prime 206182633 := by
  apply lucas_primality 206182633 (5 : ZMod 206182633)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (233, 1), (36871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (233, 1), (36871, 1)] : List FactorBlock).map factorBlockValue).prod) = 206182633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_233
      · exact prime_fortyOneAM_36871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 206182633) ^ 103091316 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 206182633) ^ 68727544 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 206182633) ^ 884904 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 206182633) ^ 5592 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_218357941 : Nat.Prime 218357941 := by
  apply lucas_primality 218357941 (6 : ZMod 218357941)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (89, 1), (103, 1), (397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (89, 1), (103, 1), (397, 1)] : List FactorBlock).map factorBlockValue).prod) = 218357941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_89
      · exact prime_fortyOneAM_103
      · exact prime_fortyOneAM_397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 218357941) ^ 109178970 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 218357941) ^ 72785980 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 218357941) ^ 43671588 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 218357941) ^ 2453460 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 218357941) ^ 2119980 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 218357941) ^ 550020 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_243417907 : Nat.Prime 243417907 := by
  apply lucas_primality 243417907 (2 : ZMod 243417907)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1051, 1), (4289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1051, 1), (4289, 1)] : List FactorBlock).map factorBlockValue).prod) = 243417907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_1051
      · exact prime_fortyOneAM_4289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243417907) ^ 121708953 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 243417907) ^ 81139302 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 243417907) ^ 231606 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 243417907) ^ 56754 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_256079711 : Nat.Prime 256079711 := by
  apply lucas_primality 256079711 (51 : ZMod 256079711)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1481, 1), (17291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1481, 1), (17291, 1)] : List FactorBlock).map factorBlockValue).prod) = 256079711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_1481
      · exact prime_fortyOneAM_17291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (51 : ZMod 256079711) ^ 128039855 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (51 : ZMod 256079711) ^ 51215942 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (51 : ZMod 256079711) ^ 172910 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (51 : ZMod 256079711) ^ 14810 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_293677067 : Nat.Prime 293677067 := by
  apply lucas_primality 293677067 (2 : ZMod 293677067)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (179, 1), (22171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (179, 1), (22171, 1)] : List FactorBlock).map factorBlockValue).prod) = 293677067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_37
      · exact prime_fortyOneAM_179
      · exact prime_fortyOneAM_22171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 293677067) ^ 146838533 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 293677067) ^ 7937218 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 293677067) ^ 1640654 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 293677067) ^ 13246 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_293864783 : Nat.Prime 293864783 := by
  apply lucas_primality 293864783 (5 : ZMod 293864783)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (146932391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (146932391, 1)] : List FactorBlock).map factorBlockValue).prod) = 293864783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_146932391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 293864783) ^ 146932391 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 293864783) ^ 2 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_298876267 : Nat.Prime 298876267 := by
  apply lucas_primality 298876267 (3 : ZMod 298876267)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (1277249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (1277249, 1)] : List FactorBlock).map factorBlockValue).prod) = 298876267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_1277249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 298876267) ^ 149438133 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 298876267) ^ 99625422 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 298876267) ^ 22990482 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 298876267) ^ 234 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_302937731 : Nat.Prime 302937731 := by
  apply lucas_primality 302937731 (6 : ZMod 302937731)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (839, 1), (36107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (839, 1), (36107, 1)] : List FactorBlock).map factorBlockValue).prod) = 302937731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_839
      · exact prime_fortyOneAM_36107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 302937731) ^ 151468865 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 302937731) ^ 60587546 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 302937731) ^ 361070 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 302937731) ^ 8390 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_307622353 : Nat.Prime 307622353 := by
  apply lucas_primality 307622353 (5 : ZMod 307622353)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (6408799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (6408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 307622353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_6408799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 307622353) ^ 153811176 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 307622353) ^ 102540784 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 307622353) ^ 48 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_332870249 : Nat.Prime 332870249 := by
  apply lucas_primality 332870249 (3 : ZMod 332870249)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41608781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41608781, 1)] : List FactorBlock).map factorBlockValue).prod) = 332870249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_41608781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 332870249) ^ 166435124 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 332870249) ^ 8 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_369629443 : Nat.Prime 369629443 := by
  apply lucas_primality 369629443 (2 : ZMod 369629443)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (13, 1), (32237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (13, 1), (32237, 1)] : List FactorBlock).map factorBlockValue).prod) = 369629443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_32237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 369629443) ^ 184814721 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 369629443) ^ 123209814 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 369629443) ^ 52804206 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 369629443) ^ 28433034 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 369629443) ^ 11466 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_453892403 : Nat.Prime 453892403 := by
  apply lucas_primality 453892403 (2 : ZMod 453892403)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (227, 1), (999763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (227, 1), (999763, 1)] : List FactorBlock).map factorBlockValue).prod) = 453892403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_227
      · exact prime_fortyOneAM_999763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 453892403) ^ 226946201 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 453892403) ^ 1999526 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 453892403) ^ 454 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_477195143 : Nat.Prime 477195143 := by
  apply lucas_primality 477195143 (5 : ZMod 477195143)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (547, 1), (11789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (547, 1), (11789, 1)] : List FactorBlock).map factorBlockValue).prod) = 477195143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_37
      · exact prime_fortyOneAM_547
      · exact prime_fortyOneAM_11789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 477195143) ^ 238597571 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 477195143) ^ 12897166 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 477195143) ^ 872386 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 477195143) ^ 40478 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_532894771 : Nat.Prime 532894771 := by
  apply lucas_primality 532894771 (3 : ZMod 532894771)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (181, 1), (32713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (181, 1), (32713, 1)] : List FactorBlock).map factorBlockValue).prod) = 532894771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_181
      · exact prime_fortyOneAM_32713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 532894771) ^ 266447385 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 532894771) ^ 177631590 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 532894771) ^ 106578954 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 532894771) ^ 2944170 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 532894771) ^ 16290 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_779923577 : Nat.Prime 779923577 := by
  apply lucas_primality 779923577 (3 : ZMod 779923577)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (97490447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (97490447, 1)] : List FactorBlock).map factorBlockValue).prod) = 779923577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_97490447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 779923577) ^ 389961788 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 779923577) ^ 8 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1063799003 : Nat.Prime 1063799003 := by
  apply lucas_primality 1063799003 (5 : ZMod 1063799003)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (8081, 1), (9403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (8081, 1), (9403, 1)] : List FactorBlock).map factorBlockValue).prod) = 1063799003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_8081
      · exact prime_fortyOneAM_9403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1063799003) ^ 531899501 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1063799003) ^ 151971286 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1063799003) ^ 131642 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1063799003) ^ 113134 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_113
      · exact prime_fortyOneAM_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1376203973 : Nat.Prime 1376203973 := by
  apply lucas_primality 1376203973 (2 : ZMod 1376203973)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (13, 1), (19, 1), (139, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (13, 1), (19, 1), (139, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) = 1376203973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_139
      · exact prime_fortyOneAM_911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1376203973) ^ 688101986 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1376203973) ^ 125109452 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1376203973) ^ 105861844 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1376203973) ^ 72431788 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1376203973) ^ 9900748 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1376203973) ^ 1510652 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1432182397 : Nat.Prime 1432182397 := by
  apply lucas_primality 1432182397 (2 : ZMod 1432182397)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (119348533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (119348533, 1)] : List FactorBlock).map factorBlockValue).prod) = 1432182397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_119348533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1432182397) ^ 716091198 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1432182397) ^ 477394132 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1432182397) ^ 12 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1486594831 : Nat.Prime 1486594831 := by
  apply lucas_primality 1486594831 (6 : ZMod 1486594831)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (1011289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (1011289, 1)] : List FactorBlock).map factorBlockValue).prod) = 1486594831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_1011289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1486594831) ^ 743297415 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1486594831) ^ 495531610 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1486594831) ^ 297318966 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1486594831) ^ 212370690 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1486594831) ^ 1470 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1576663789 : Nat.Prime 1576663789 := by
  apply lucas_primality 1576663789 (14 : ZMod 1576663789)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (887, 1), (3023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (887, 1), (3023, 1)] : List FactorBlock).map factorBlockValue).prod) = 1576663789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_887
      · exact prime_fortyOneAM_3023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1576663789) ^ 788331894 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (14 : ZMod 1576663789) ^ 525554596 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (14 : ZMod 1576663789) ^ 225237684 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (14 : ZMod 1576663789) ^ 1777524 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (14 : ZMod 1576663789) ^ 521556 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1824813733 : Nat.Prime 1824813733 := by
  apply lucas_primality 1824813733 (2 : ZMod 1824813733)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (19, 1), (41, 1), (79, 1), (353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (19, 1), (41, 1), (79, 1), (353, 1)] : List FactorBlock).map factorBlockValue).prod) = 1824813733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_41
      · exact prime_fortyOneAM_79
      · exact prime_fortyOneAM_353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1824813733) ^ 912406866 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1824813733) ^ 608271244 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1824813733) ^ 260687676 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1824813733) ^ 96042828 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1824813733) ^ 44507652 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1824813733) ^ 23098908 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1824813733) ^ 5169444 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_2185762511 : Nat.Prime 2185762511 := by
  apply lucas_primality 2185762511 (7 : ZMod 2185762511)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (131, 1), (1668521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (131, 1), (1668521, 1)] : List FactorBlock).map factorBlockValue).prod) = 2185762511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_131
      · exact prime_fortyOneAM_1668521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2185762511) ^ 1092881255 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2185762511) ^ 437152502 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2185762511) ^ 16685210 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2185762511) ^ 1310 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_2351480777 : Nat.Prime 2351480777 := by
  apply lucas_primality 2351480777 (3 : ZMod 2351480777)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (67, 1), (151279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (67, 1), (151279, 1)] : List FactorBlock).map factorBlockValue).prod) = 2351480777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_67
      · exact prime_fortyOneAM_151279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2351480777) ^ 1175740388 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2351480777) ^ 81085544 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2351480777) ^ 35096728 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2351480777) ^ 15544 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_2374229903 : Nat.Prime 2374229903 := by
  apply lucas_primality 2374229903 (5 : ZMod 2374229903)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1093, 1), (98737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1093, 1), (98737, 1)] : List FactorBlock).map factorBlockValue).prod) = 2374229903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_1093
      · exact prime_fortyOneAM_98737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2374229903) ^ 1187114951 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2374229903) ^ 215839082 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2374229903) ^ 2172214 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2374229903) ^ 24046 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_2374552097 : Nat.Prime 2374552097 := by
  apply lucas_primality 2374552097 (3 : ZMod 2374552097)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (10600679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (10600679, 1)] : List FactorBlock).map factorBlockValue).prod) = 2374552097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_10600679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2374552097) ^ 1187276048 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2374552097) ^ 339221728 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2374552097) ^ 224 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_2662961993 : Nat.Prime 2662961993 := by
  apply lucas_primality 2662961993 (3 : ZMod 2662961993)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (332870249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (332870249, 1)] : List FactorBlock).map factorBlockValue).prod) = 2662961993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_332870249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2662961993) ^ 1331480996 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2662961993) ^ 8 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_2813497301 : Nat.Prime 2813497301 := by
  apply lucas_primality 2813497301 (2 : ZMod 2813497301)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (2657, 1), (10589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (2657, 1), (10589, 1)] : List FactorBlock).map factorBlockValue).prod) = 2813497301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_2657
      · exact prime_fortyOneAM_10589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2813497301) ^ 1406748650 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2813497301) ^ 562699460 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2813497301) ^ 1058900 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2813497301) ^ 265700 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_3197368627 : Nat.Prime 3197368627 := by
  apply lucas_primality 3197368627 (2 : ZMod 3197368627)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (532894771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (532894771, 1)] : List FactorBlock).map factorBlockValue).prod) = 3197368627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_532894771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3197368627) ^ 1598684313 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3197368627) ^ 1065789542 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3197368627) ^ 6 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_3667245859 : Nat.Prime 3667245859 := by
  apply lucas_primality 3667245859 (3 : ZMod 3667245859)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (203735881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (203735881, 1)] : List FactorBlock).map factorBlockValue).prod) = 3667245859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_203735881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3667245859) ^ 1833622929 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3667245859) ^ 1222415286 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3667245859) ^ 18 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_3872145691 : Nat.Prime 3872145691 := by
  apply lucas_primality 3872145691 (2 : ZMod 3872145691)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (739, 1), (8317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (739, 1), (8317, 1)] : List FactorBlock).map factorBlockValue).prod) = 3872145691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_739
      · exact prime_fortyOneAM_8317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3872145691) ^ 1936072845 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3872145691) ^ 1290715230 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3872145691) ^ 774429138 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3872145691) ^ 553163670 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3872145691) ^ 5239710 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3872145691) ^ 465570 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_5244604007 : Nat.Prime 5244604007 := by
  apply lucas_primality 5244604007 (5 : ZMod 5244604007)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (29, 1), (199, 1), (26729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (29, 1), (199, 1), (26729, 1)] : List FactorBlock).map factorBlockValue).prod) = 5244604007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_199
      · exact prime_fortyOneAM_26729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5244604007) ^ 2622302003 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5244604007) ^ 308506118 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5244604007) ^ 180848414 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5244604007) ^ 26354794 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5244604007) ^ 196214 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_5768510291 : Nat.Prime 5768510291 := by
  apply lucas_primality 5768510291 (2 : ZMod 5768510291)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (15121, 1), (38149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (15121, 1), (38149, 1)] : List FactorBlock).map factorBlockValue).prod) = 5768510291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_15121
      · exact prime_fortyOneAM_38149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5768510291) ^ 2884255145 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5768510291) ^ 1153702058 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5768510291) ^ 381490 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5768510291) ^ 151210 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_8084908681 : Nat.Prime 8084908681 := by
  apply lucas_primality 8084908681 (7 : ZMod 8084908681)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (67374239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (67374239, 1)] : List FactorBlock).map factorBlockValue).prod) = 8084908681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_67374239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 8084908681) ^ 4042454340 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 8084908681) ^ 2694969560 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 8084908681) ^ 1616981736 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 8084908681) ^ 120 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_10326426139 : Nat.Prime 10326426139 := by
  apply lucas_primality 10326426139 (17 : ZMod 10326426139)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (81955763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (81955763, 1)] : List FactorBlock).map factorBlockValue).prod) = 10326426139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_81955763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 10326426139) ^ 5163213069 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (17 : ZMod 10326426139) ^ 3442142046 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (17 : ZMod 10326426139) ^ 1475203734 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (17 : ZMod 10326426139) ^ 126 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_12336546671 : Nat.Prime 12336546671 := by
  apply lucas_primality 12336546671 (11 : ZMod 12336546671)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (19, 1), (61, 1), (73, 1), (2083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (19, 1), (61, 1), (73, 1), (2083, 1)] : List FactorBlock).map factorBlockValue).prod) = 12336546671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_61
      · exact prime_fortyOneAM_73
      · exact prime_fortyOneAM_2083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 12336546671) ^ 6168273335 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 12336546671) ^ 2467309334 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 12336546671) ^ 1762363810 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 12336546671) ^ 649291930 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 12336546671) ^ 202238470 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 12336546671) ^ 168993790 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 12336546671) ^ 5922490 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_12759239747 : Nat.Prime 12759239747 := by
  apply lucas_primality 12759239747 (5 : ZMod 12759239747)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (30524497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (30524497, 1)] : List FactorBlock).map factorBlockValue).prod) = 12759239747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_30524497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 12759239747) ^ 6379619873 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 12759239747) ^ 1159930886 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 12759239747) ^ 671538934 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 12759239747) ^ 418 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_12943385729 : Nat.Prime 12943385729 := by
  apply lucas_primality 12943385729 (12 : ZMod 12943385729)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (13, 1), (1111211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (13, 1), (1111211, 1)] : List FactorBlock).map factorBlockValue).prod) = 12943385729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_1111211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (12 : ZMod 12943385729) ^ 6471692864 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (12 : ZMod 12943385729) ^ 1849055104 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (12 : ZMod 12943385729) ^ 995645056 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (12 : ZMod 12943385729) ^ 11648 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_15977771959 : Nat.Prime 15977771959 := by
  apply lucas_primality 15977771959 (3 : ZMod 15977771959)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2662961993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2662961993, 1)] : List FactorBlock).map factorBlockValue).prod) = 15977771959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_2662961993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 15977771959) ^ 7988885979 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 15977771959) ^ 5325923986 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 15977771959) ^ 6 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_18345475909 : Nat.Prime 18345475909 := by
  apply lucas_primality 18345475909 (2 : ZMod 18345475909)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (4793, 1), (106321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (4793, 1), (106321, 1)] : List FactorBlock).map factorBlockValue).prod) = 18345475909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_4793
      · exact prime_fortyOneAM_106321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18345475909) ^ 9172737954 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 18345475909) ^ 6115158636 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 18345475909) ^ 3827556 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 18345475909) ^ 172548 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_19266855623 : Nat.Prime 19266855623 := by
  apply lucas_primality 19266855623 (5 : ZMod 19266855623)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1376203973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1376203973, 1)] : List FactorBlock).map factorBlockValue).prod) = 19266855623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_1376203973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 19266855623) ^ 9633427811 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 19266855623) ^ 2752407946 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 19266855623) ^ 14 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_20037513329 : Nat.Prime 20037513329 := by
  apply lucas_primality 20037513329 (3 : ZMod 20037513329)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (178906369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (178906369, 1)] : List FactorBlock).map factorBlockValue).prod) = 20037513329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_178906369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20037513329) ^ 10018756664 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 20037513329) ^ 2862501904 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 20037513329) ^ 112 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_20291582887 : Nat.Prime 20291582887 := by
  apply lucas_primality 20291582887 (3 : ZMod 20291582887)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (16631, 1), (203351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (16631, 1), (203351, 1)] : List FactorBlock).map factorBlockValue).prod) = 20291582887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_16631
      · exact prime_fortyOneAM_203351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 20291582887) ^ 10145791443 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 20291582887) ^ 6763860962 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 20291582887) ^ 1220106 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 20291582887) ^ 99786 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_22508226817 : Nat.Prime 22508226817 := by
  apply lucas_primality 22508226817 (7 : ZMod 22508226817)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (29307587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (29307587, 1)] : List FactorBlock).map factorBlockValue).prod) = 22508226817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_29307587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 22508226817) ^ 11254113408 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 22508226817) ^ 7502742272 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 22508226817) ^ 768 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_24066546167 : Nat.Prime 24066546167 := by
  apply lucas_primality 24066546167 (10 : ZMod 24066546167)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (4483, 1), (206477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (4483, 1), (206477, 1)] : List FactorBlock).map factorBlockValue).prod) = 24066546167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_4483
      · exact prime_fortyOneAM_206477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 24066546167) ^ 12033273083 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 24066546167) ^ 1851272782 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 24066546167) ^ 5368402 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 24066546167) ^ 116558 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_24673093343 : Nat.Prime 24673093343 := by
  apply lucas_primality 24673093343 (5 : ZMod 24673093343)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12336546671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12336546671, 1)] : List FactorBlock).map factorBlockValue).prod) = 24673093343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_12336546671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 24673093343) ^ 12336546671 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 24673093343) ^ 2 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_27656608789 : Nat.Prime 27656608789 := by
  apply lucas_primality 27656608789 (6 : ZMod 27656608789)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (256079711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (256079711, 1)] : List FactorBlock).map factorBlockValue).prod) = 27656608789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_256079711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 27656608789) ^ 13828304394 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 27656608789) ^ 9218869596 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 27656608789) ^ 108 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_28001123627 : Nat.Prime 28001123627 := by
  apply lucas_primality 28001123627 (2 : ZMod 28001123627)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (433, 1), (4619123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (433, 1), (4619123, 1)] : List FactorBlock).map factorBlockValue).prod) = 28001123627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_433
      · exact prime_fortyOneAM_4619123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28001123627) ^ 14000561813 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 28001123627) ^ 4000160518 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 28001123627) ^ 64667722 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 28001123627) ^ 6062 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_28712733319 : Nat.Prime 28712733319 := by
  apply lucas_primality 28712733319 (3 : ZMod 28712733319)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (83, 1), (19218697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (83, 1), (19218697, 1)] : List FactorBlock).map factorBlockValue).prod) = 28712733319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_83
      · exact prime_fortyOneAM_19218697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 28712733319) ^ 14356366659 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 28712733319) ^ 9570911106 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 28712733319) ^ 345936546 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 28712733319) ^ 1494 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_30339099761 : Nat.Prime 30339099761 := by
  apply lucas_primality 30339099761 (3 : ZMod 30339099761)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (239, 1), (1586773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (239, 1), (1586773, 1)] : List FactorBlock).map factorBlockValue).prod) = 30339099761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_239
      · exact prime_fortyOneAM_1586773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 30339099761) ^ 15169549880 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 30339099761) ^ 6067819952 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 30339099761) ^ 126941840 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 30339099761) ^ 19120 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_32362974499 : Nat.Prime 32362974499 := by
  apply lucas_primality 32362974499 (3 : ZMod 32362974499)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35747, 1), (150889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35747, 1), (150889, 1)] : List FactorBlock).map factorBlockValue).prod) = 32362974499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_35747
      · exact prime_fortyOneAM_150889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 32362974499) ^ 16181487249 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 32362974499) ^ 10787658166 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 32362974499) ^ 905334 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 32362974499) ^ 214482 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_48687909427 : Nat.Prime 48687909427 := by
  apply lucas_primality 48687909427 (5 : ZMod 48687909427)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (41, 1), (179, 1), (28351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (41, 1), (179, 1), (28351, 1)] : List FactorBlock).map factorBlockValue).prod) = 48687909427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_41
      · exact prime_fortyOneAM_179
      · exact prime_fortyOneAM_28351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 48687909427) ^ 24343954713 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 48687909427) ^ 16229303142 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 48687909427) ^ 3745223802 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 48687909427) ^ 1187509986 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 48687909427) ^ 271999494 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 48687909427) ^ 1717326 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_57201027461 : Nat.Prime 57201027461 := by
  apply lucas_primality 57201027461 (2 : ZMod 57201027461)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (59, 1), (1229, 1), (39443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (59, 1), (1229, 1), (39443, 1)] : List FactorBlock).map factorBlockValue).prod) = 57201027461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_59
      · exact prime_fortyOneAM_1229
      · exact prime_fortyOneAM_39443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57201027461) ^ 28600513730 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 57201027461) ^ 11440205492 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 57201027461) ^ 969508940 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 57201027461) ^ 46542740 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 57201027461) ^ 1450220 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_64790751973 : Nat.Prime 64790751973 := by
  apply lucas_primality 64790751973 (2 : ZMod 64790751973)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (739, 1), (7306129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (739, 1), (7306129, 1)] : List FactorBlock).map factorBlockValue).prod) = 64790751973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_739
      · exact prime_fortyOneAM_7306129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 64790751973) ^ 32395375986 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 64790751973) ^ 21596917324 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 64790751973) ^ 87673548 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 64790751973) ^ 8868 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_65295981319 : Nat.Prime 65295981319 := by
  apply lucas_primality 65295981319 (3 : ZMod 65295981319)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (181, 1), (1939523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (181, 1), (1939523, 1)] : List FactorBlock).map factorBlockValue).prod) = 65295981319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_31
      · exact prime_fortyOneAM_181
      · exact prime_fortyOneAM_1939523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65295981319) ^ 32647990659 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 65295981319) ^ 21765327106 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 65295981319) ^ 2106321978 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 65295981319) ^ 360751278 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 65295981319) ^ 33666 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_66499146733 : Nat.Prime 66499146733 := by
  apply lucas_primality 66499146733 (5 : ZMod 66499146733)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (149772853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (149772853, 1)] : List FactorBlock).map factorBlockValue).prod) = 66499146733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_37
      · exact prime_fortyOneAM_149772853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66499146733) ^ 33249573366 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 66499146733) ^ 22166382244 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 66499146733) ^ 1797274236 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 66499146733) ^ 444 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_88848457573 : Nat.Prime 88848457573 := by
  apply lucas_primality 88848457573 (2 : ZMod 88848457573)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 5), (601, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 5), (601, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) = 88848457573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_601
      · exact prime_fortyOneAM_733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 88848457573) ^ 44424228786 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 88848457573) ^ 29616152524 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 88848457573) ^ 12692636796 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 88848457573) ^ 147834372 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 88848457573) ^ 121212084 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_113319125603 : Nat.Prime 113319125603 := by
  apply lucas_primality 113319125603 (2 : ZMod 113319125603)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2287, 1), (24774623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2287, 1), (24774623, 1)] : List FactorBlock).map factorBlockValue).prod) = 113319125603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_2287
      · exact prime_fortyOneAM_24774623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 113319125603) ^ 56659562801 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 113319125603) ^ 49549246 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 113319125603) ^ 4574 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_120851980049 : Nat.Prime 120851980049 := by
  apply lucas_primality 120851980049 (3 : ZMod 120851980049)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (73, 1), (1021, 1), (101341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (73, 1), (1021, 1), (101341, 1)] : List FactorBlock).map factorBlockValue).prod) = 120851980049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_73
      · exact prime_fortyOneAM_1021
      · exact prime_fortyOneAM_101341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 120851980049) ^ 60425990024 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 120851980049) ^ 1655506576 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 120851980049) ^ 118366288 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 120851980049) ^ 1192528 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_144244385563 : Nat.Prime 144244385563 := by
  apply lucas_primality 144244385563 (2 : ZMod 144244385563)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8161, 1), (2945807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8161, 1), (2945807, 1)] : List FactorBlock).map factorBlockValue).prod) = 144244385563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_8161
      · exact prime_fortyOneAM_2945807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 144244385563) ^ 72122192781 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 144244385563) ^ 48081461854 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 144244385563) ^ 17674842 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 144244385563) ^ 48966 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_159796002313 : Nat.Prime 159796002313 := by
  apply lucas_primality 159796002313 (5 : ZMod 159796002313)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (31, 1), (7954799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (31, 1), (7954799, 1)] : List FactorBlock).map factorBlockValue).prod) = 159796002313 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_31
      · exact prime_fortyOneAM_7954799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 159796002313) ^ 79898001156 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 159796002313) ^ 53265334104 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 159796002313) ^ 5154709752 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 159796002313) ^ 20088 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_160429405141 : Nat.Prime 160429405141 := by
  apply lucas_primality 160429405141 (6 : ZMod 160429405141)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (59, 1), (179, 1), (9377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (59, 1), (179, 1), (9377, 1)] : List FactorBlock).map factorBlockValue).prod) = 160429405141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_59
      · exact prime_fortyOneAM_179
      · exact prime_fortyOneAM_9377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 160429405141) ^ 80214702570 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 160429405141) ^ 53476468380 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 160429405141) ^ 32085881028 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 160429405141) ^ 2719142460 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 160429405141) ^ 896253660 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 160429405141) ^ 17108820 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_188229778547 : Nat.Prime 188229778547 := by
  apply lucas_primality 188229778547 (2 : ZMod 188229778547)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (173, 1), (9547, 1), (56983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (173, 1), (9547, 1), (56983, 1)] : List FactorBlock).map factorBlockValue).prod) = 188229778547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_173
      · exact prime_fortyOneAM_9547
      · exact prime_fortyOneAM_56983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 188229778547) ^ 94114889273 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 188229778547) ^ 1088033402 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 188229778547) ^ 19716118 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 188229778547) ^ 3303262 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_188886633517 : Nat.Prime 188886633517 := by
  apply lucas_primality 188886633517 (2 : ZMod 188886633517)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (19, 1), (139, 1), (283813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (19, 1), (139, 1), (283813, 1)] : List FactorBlock).map factorBlockValue).prod) = 188886633517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_139
      · exact prime_fortyOneAM_283813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 188886633517) ^ 94443316758 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 188886633517) ^ 62962211172 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 188886633517) ^ 26983804788 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 188886633517) ^ 9941401764 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 188886633517) ^ 1358896644 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 188886633517) ^ 665532 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_196593604091 : Nat.Prime 196593604091 := by
  apply lucas_primality 196593604091 (2 : ZMod 196593604091)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (7177, 1), (210709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (7177, 1), (210709, 1)] : List FactorBlock).map factorBlockValue).prod) = 196593604091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_7177
      · exact prime_fortyOneAM_210709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 196593604091) ^ 98296802045 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 196593604091) ^ 39318720818 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 196593604091) ^ 15122584930 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 196593604091) ^ 27392170 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 196593604091) ^ 933010 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_204040523339 : Nat.Prime 204040523339 := by
  apply lucas_primality 204040523339 (2 : ZMod 204040523339)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (16759, 1), (47933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (16759, 1), (47933, 1)] : List FactorBlock).map factorBlockValue).prod) = 204040523339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_127
      · exact prime_fortyOneAM_16759
      · exact prime_fortyOneAM_47933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 204040523339) ^ 102020261669 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 204040523339) ^ 1606618294 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 204040523339) ^ 12174982 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 204040523339) ^ 4256786 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_226318511977 : Nat.Prime 226318511977 := by
  apply lucas_primality 226318511977 (5 : ZMod 226318511977)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4783, 1), (1971553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4783, 1), (1971553, 1)] : List FactorBlock).map factorBlockValue).prod) = 226318511977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_4783
      · exact prime_fortyOneAM_1971553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 226318511977) ^ 113159255988 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 226318511977) ^ 75439503992 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 226318511977) ^ 47317272 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 226318511977) ^ 114792 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_278689935443 : Nat.Prime 278689935443 := by
  apply lucas_primality 278689935443 (2 : ZMod 278689935443)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (307, 1), (453892403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (307, 1), (453892403, 1)] : List FactorBlock).map factorBlockValue).prod) = 278689935443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_307
      · exact prime_fortyOneAM_453892403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 278689935443) ^ 139344967721 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 278689935443) ^ 907784806 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 278689935443) ^ 614 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_282387356429 : Nat.Prime 282387356429 := by
  apply lucas_primality 282387356429 (2 : ZMod 282387356429)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 1), (1723, 1), (375901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 1), (1723, 1), (375901, 1)] : List FactorBlock).map factorBlockValue).prod) = 282387356429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_109
      · exact prime_fortyOneAM_1723
      · exact prime_fortyOneAM_375901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 282387356429) ^ 141193678214 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 282387356429) ^ 2590709692 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 282387356429) ^ 163892836 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 282387356429) ^ 751228 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_305503137491 : Nat.Prime 305503137491 := by
  apply lucas_primality 305503137491 (2 : ZMod 305503137491)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (59443, 1), (513943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (59443, 1), (513943, 1)] : List FactorBlock).map factorBlockValue).prod) = 305503137491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_59443
      · exact prime_fortyOneAM_513943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 305503137491) ^ 152751568745 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 305503137491) ^ 61100627498 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 305503137491) ^ 5139430 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 305503137491) ^ 594430 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_360544746701 : Nat.Prime 360544746701 := by
  apply lucas_primality 360544746701 (3 : ZMod 360544746701)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (19, 1), (31, 1), (373, 1), (16411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (19, 1), (31, 1), (373, 1), (16411, 1)] : List FactorBlock).map factorBlockValue).prod) = 360544746701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_31
      · exact prime_fortyOneAM_373
      · exact prime_fortyOneAM_16411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 360544746701) ^ 180272373350 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 360544746701) ^ 72108949340 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 360544746701) ^ 18976039300 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 360544746701) ^ 11630475700 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 360544746701) ^ 966607900 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 360544746701) ^ 21969700 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_397
      · exact prime_fortyOneAM_2531
      · exact prime_fortyOneAM_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_583458069907 : Nat.Prime 583458069907 := by
  apply lucas_primality 583458069907 (3 : ZMod 583458069907)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (107, 1), (302937731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (107, 1), (302937731, 1)] : List FactorBlock).map factorBlockValue).prod) = 583458069907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_107
      · exact prime_fortyOneAM_302937731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 583458069907) ^ 291729034953 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 583458069907) ^ 194486023302 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 583458069907) ^ 5452879158 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 583458069907) ^ 1926 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_623203352237 : Nat.Prime 623203352237 := by
  apply lucas_primality 623203352237 (2 : ZMod 623203352237)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (997, 1), (7817, 1), (19991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (997, 1), (7817, 1), (19991, 1)] : List FactorBlock).map factorBlockValue).prod) = 623203352237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_997
      · exact prime_fortyOneAM_7817
      · exact prime_fortyOneAM_19991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 623203352237) ^ 311601676118 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 623203352237) ^ 625078588 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 623203352237) ^ 79724108 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 623203352237) ^ 31174196 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_634009534427 : Nat.Prime 634009534427 := by
  apply lucas_primality 634009534427 (2 : ZMod 634009534427)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (167, 1), (21328451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (167, 1), (21328451, 1)] : List FactorBlock).map factorBlockValue).prod) = 634009534427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_89
      · exact prime_fortyOneAM_167
      · exact prime_fortyOneAM_21328451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 634009534427) ^ 317004767213 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 634009534427) ^ 7123702634 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 634009534427) ^ 3796464278 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 634009534427) ^ 29726 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_659038097873 : Nat.Prime 659038097873 := by
  apply lucas_primality 659038097873 (3 : ZMod 659038097873)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (11, 1), (89, 1), (6010489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (11, 1), (89, 1), (6010489, 1)] : List FactorBlock).map factorBlockValue).prod) = 659038097873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_89
      · exact prime_fortyOneAM_6010489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 659038097873) ^ 329519048936 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 659038097873) ^ 94148299696 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 659038097873) ^ 59912554352 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 659038097873) ^ 7404922448 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 659038097873) ^ 109648 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_719141144749 : Nat.Prime 719141144749 := by
  apply lucas_primality 719141144749 (7 : ZMod 719141144749)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (509, 1), (9056737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (509, 1), (9056737, 1)] : List FactorBlock).map factorBlockValue).prod) = 719141144749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_509
      · exact prime_fortyOneAM_9056737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 719141144749) ^ 359570572374 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 719141144749) ^ 239713714916 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 719141144749) ^ 55318549596 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 719141144749) ^ 1412850972 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 719141144749) ^ 79404 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1097740871221 : Nat.Prime 1097740871221 := by
  apply lucas_primality 1097740871221 (6 : ZMod 1097740871221)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (769, 1), (839, 1), (4051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (769, 1), (839, 1), (4051, 1)] : List FactorBlock).map factorBlockValue).prod) = 1097740871221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_769
      · exact prime_fortyOneAM_839
      · exact prime_fortyOneAM_4051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1097740871221) ^ 548870435610 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1097740871221) ^ 365913623740 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1097740871221) ^ 219548174244 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1097740871221) ^ 156820124460 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1097740871221) ^ 1427491380 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1097740871221) ^ 1308391980 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1097740871221) ^ 270980220 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1450223760589 : Nat.Prime 1450223760589 := by
  apply lucas_primality 1450223760589 (2 : ZMod 1450223760589)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (120851980049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (120851980049, 1)] : List FactorBlock).map factorBlockValue).prod) = 1450223760589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_120851980049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1450223760589) ^ 725111880294 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1450223760589) ^ 483407920196 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1450223760589) ^ 12 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1489347175447 : Nat.Prime 1489347175447 := by
  apply lucas_primality 1489347175447 (6 : ZMod 1489347175447)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (13, 1), (73, 1), (3229189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (13, 1), (73, 1), (3229189, 1)] : List FactorBlock).map factorBlockValue).prod) = 1489347175447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_73
      · exact prime_fortyOneAM_3229189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1489347175447) ^ 744673587723 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1489347175447) ^ 496449058482 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1489347175447) ^ 114565167342 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1489347175447) ^ 20402016102 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1489347175447) ^ 461214 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_35279
      · exact prime_fortyOneAM_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1668568573253 : Nat.Prime 1668568573253 := by
  apply lucas_primality 1668568573253 (2 : ZMod 1668568573253)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (67, 1), (29153, 1), (30509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (67, 1), (29153, 1), (30509, 1)] : List FactorBlock).map factorBlockValue).prod) = 1668568573253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_67
      · exact prime_fortyOneAM_29153
      · exact prime_fortyOneAM_30509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1668568573253) ^ 834284286626 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1668568573253) ^ 238366939036 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1668568573253) ^ 24904008556 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1668568573253) ^ 57234884 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1668568573253) ^ 54691028 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1694936056097 : Nat.Prime 1694936056097 := by
  apply lucas_primality 1694936056097 (3 : ZMod 1694936056097)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (349, 1), (383, 1), (396259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (349, 1), (383, 1), (396259, 1)] : List FactorBlock).map factorBlockValue).prod) = 1694936056097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_349
      · exact prime_fortyOneAM_383
      · exact prime_fortyOneAM_396259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1694936056097) ^ 847468028048 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1694936056097) ^ 4856550304 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1694936056097) ^ 4425420512 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1694936056097) ^ 4277344 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1994649602389 : Nat.Prime 1994649602389 := by
  apply lucas_primality 1994649602389 (2 : ZMod 1994649602389)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (29, 1), (73, 1), (3413789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (29, 1), (73, 1), (3413789, 1)] : List FactorBlock).map factorBlockValue).prod) = 1994649602389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_73
      · exact prime_fortyOneAM_3413789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1994649602389) ^ 997324801194 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1994649602389) ^ 664883200796 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1994649602389) ^ 86723895756 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1994649602389) ^ 68781020772 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1994649602389) ^ 27323967156 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1994649602389) ^ 584292 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_2013099773471 : Nat.Prime 2013099773471 := by
  apply lucas_primality 2013099773471 (13 : ZMod 2013099773471)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (541, 1), (12003457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (541, 1), (12003457, 1)] : List FactorBlock).map factorBlockValue).prod) = 2013099773471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_31
      · exact prime_fortyOneAM_541
      · exact prime_fortyOneAM_12003457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2013099773471) ^ 1006549886735 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (13 : ZMod 2013099773471) ^ 402619954694 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (13 : ZMod 2013099773471) ^ 64938702370 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (13 : ZMod 2013099773471) ^ 3721071670 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (13 : ZMod 2013099773471) ^ 167710 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_2132362981753 : Nat.Prime 2132362981753 := by
  apply lucas_primality 2132362981753 (17 : ZMod 2132362981753)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (88848457573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (88848457573, 1)] : List FactorBlock).map factorBlockValue).prod) = 2132362981753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_88848457573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 2132362981753) ^ 1066181490876 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (17 : ZMod 2132362981753) ^ 710787660584 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (17 : ZMod 2132362981753) ^ 24 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_2986913749213 : Nat.Prime 2986913749213 := by
  apply lucas_primality 2986913749213 (2 : ZMod 2986913749213)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (27656608789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (27656608789, 1)] : List FactorBlock).map factorBlockValue).prod) = 2986913749213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_27656608789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2986913749213) ^ 1493456874606 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2986913749213) ^ 995637916404 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2986913749213) ^ 108 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_3348061788191 : Nat.Prime 3348061788191 := by
  apply lucas_primality 3348061788191 (7 : ZMod 3348061788191)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (17, 1), (2813497301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (17, 1), (2813497301, 1)] : List FactorBlock).map factorBlockValue).prod) = 3348061788191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_2813497301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3348061788191) ^ 1674030894095 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 3348061788191) ^ 669612357638 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 3348061788191) ^ 478294541170 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 3348061788191) ^ 196944811070 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 3348061788191) ^ 1190 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_5499056474839 : Nat.Prime 5499056474839 := by
  apply lucas_primality 5499056474839 (3 : ZMod 5499056474839)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (305503137491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (305503137491, 1)] : List FactorBlock).map factorBlockValue).prod) = 5499056474839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_305503137491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5499056474839) ^ 2749528237419 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5499056474839) ^ 1833018824946 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5499056474839) ^ 18 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_5710825188091 : Nat.Prime 5710825188091 := by
  apply lucas_primality 5710825188091 (7 : ZMod 5710825188091)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (5768510291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (5768510291, 1)] : List FactorBlock).map factorBlockValue).prod) = 5710825188091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_5768510291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5710825188091) ^ 2855412594045 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 5710825188091) ^ 1903608396030 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 5710825188091) ^ 1142165037618 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 5710825188091) ^ 519165926190 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 5710825188091) ^ 990 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_5846307133193 : Nat.Prime 5846307133193 := by
  apply lucas_primality 5846307133193 (3 : ZMod 5846307133193)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (937, 1), (779923577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (937, 1), (779923577, 1)] : List FactorBlock).map factorBlockValue).prod) = 5846307133193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_937
      · exact prime_fortyOneAM_779923577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5846307133193) ^ 2923153566596 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5846307133193) ^ 6239388616 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5846307133193) ^ 7496 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_6614448127613 : Nat.Prime 6614448127613 := by
  apply lucas_primality 6614448127613 (2 : ZMod 6614448127613)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (7043, 1), (18060617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (7043, 1), (18060617, 1)] : List FactorBlock).map factorBlockValue).prod) = 6614448127613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_7043
      · exact prime_fortyOneAM_18060617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6614448127613) ^ 3307224063806 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6614448127613) ^ 508803702124 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6614448127613) ^ 939152084 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6614448127613) ^ 366236 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_6652289282297 : Nat.Prime 6652289282297 := by
  apply lucas_primality 6652289282297 (5 : ZMod 6652289282297)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (131, 1), (337, 1), (2690803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (131, 1), (337, 1), (2690803, 1)] : List FactorBlock).map factorBlockValue).prod) = 6652289282297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_131
      · exact prime_fortyOneAM_337
      · exact prime_fortyOneAM_2690803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6652289282297) ^ 3326144641148 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 6652289282297) ^ 950327040328 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 6652289282297) ^ 50780834216 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 6652289282297) ^ 19739730808 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 6652289282297) ^ 2472232 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_6777296554297 : Nat.Prime 6777296554297 := by
  apply lucas_primality 6777296554297 (7 : ZMod 6777296554297)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (282387356429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (282387356429, 1)] : List FactorBlock).map factorBlockValue).prod) = 6777296554297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_282387356429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6777296554297) ^ 3388648277148 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 6777296554297) ^ 2259098851432 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 6777296554297) ^ 24 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_13228896255227 : Nat.Prime 13228896255227 := by
  apply lucas_primality 13228896255227 (2 : ZMod 13228896255227)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6614448127613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6614448127613, 1)] : List FactorBlock).map factorBlockValue).prod) = 13228896255227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_6614448127613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 13228896255227) ^ 6614448127613 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13228896255227) ^ 2 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_13357308358237 : Nat.Prime 13357308358237 := by
  apply lucas_primality 13357308358237 (6 : ZMod 13357308358237)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (261581, 1), (4255313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (261581, 1), (4255313, 1)] : List FactorBlock).map factorBlockValue).prod) = 13357308358237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_261581
      · exact prime_fortyOneAM_4255313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 13357308358237) ^ 6678654179118 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 13357308358237) ^ 4452436119412 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 13357308358237) ^ 51063756 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 13357308358237) ^ 3138972 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_14065512902851 : Nat.Prime 14065512902851 := by
  apply lucas_primality 14065512902851 (11 : ZMod 14065512902851)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (278581, 1), (336599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (278581, 1), (336599, 1)] : List FactorBlock).map factorBlockValue).prod) = 14065512902851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_278581
      · exact prime_fortyOneAM_336599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 14065512902851) ^ 7032756451425 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 14065512902851) ^ 4688504300950 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 14065512902851) ^ 2813102580570 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 14065512902851) ^ 50489850 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 14065512902851) ^ 41787150 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_15793938967453 : Nat.Prime 15793938967453 := by
  apply lucas_primality 15793938967453 (2 : ZMod 15793938967453)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (71, 1), (17137, 1), (1081723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (71, 1), (17137, 1), (1081723, 1)] : List FactorBlock).map factorBlockValue).prod) = 15793938967453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_71
      · exact prime_fortyOneAM_17137
      · exact prime_fortyOneAM_1081723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15793938967453) ^ 7896969483726 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15793938967453) ^ 5264646322484 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15793938967453) ^ 222449844612 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15793938967453) ^ 921627996 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15793938967453) ^ 14600724 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_19505107163239 : Nat.Prime 19505107163239 := by
  apply lucas_primality 19505107163239 (6 : ZMod 19505107163239)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (271, 1), (2087, 1), (5747849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (271, 1), (2087, 1), (5747849, 1)] : List FactorBlock).map factorBlockValue).prod) = 19505107163239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_271
      · exact prime_fortyOneAM_2087
      · exact prime_fortyOneAM_5747849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 19505107163239) ^ 9752553581619 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 19505107163239) ^ 6501702387746 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 19505107163239) ^ 71974565178 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 19505107163239) ^ 9346002474 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 19505107163239) ^ 3393462 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_24516853948549 : Nat.Prime 24516853948549 := by
  apply lucas_primality 24516853948549 (2 : ZMod 24516853948549)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (23, 1), (977, 1), (777097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (23, 1), (977, 1), (777097, 1)] : List FactorBlock).map factorBlockValue).prod) = 24516853948549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_977
      · exact prime_fortyOneAM_777097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24516853948549) ^ 12258426974274 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 24516853948549) ^ 8172284649516 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 24516853948549) ^ 1885911842196 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 24516853948549) ^ 1065950171676 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 24516853948549) ^ 25094016324 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 24516853948549) ^ 31549284 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_30121875068669 : Nat.Prime 30121875068669 := by
  apply lucas_primality 30121875068669 (2 : ZMod 30121875068669)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (227, 1), (7451, 1), (193577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (227, 1), (7451, 1), (193577, 1)] : List FactorBlock).map factorBlockValue).prod) = 30121875068669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_227
      · exact prime_fortyOneAM_7451
      · exact prime_fortyOneAM_193577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30121875068669) ^ 15060937534334 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30121875068669) ^ 1309646742116 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30121875068669) ^ 132695484884 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30121875068669) ^ 4042662068 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30121875068669) ^ 155606684 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_34936544158643 : Nat.Prime 34936544158643 := by
  apply lucas_primality 34936544158643 (2 : ZMod 34936544158643)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (883, 1), (15269, 1), (185089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (883, 1), (15269, 1), (185089, 1)] : List FactorBlock).map factorBlockValue).prod) = 34936544158643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_883
      · exact prime_fortyOneAM_15269
      · exact prime_fortyOneAM_185089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34936544158643) ^ 17468272079321 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 34936544158643) ^ 4990934879806 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 34936544158643) ^ 39565735174 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 34936544158643) ^ 2288070218 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 34936544158643) ^ 188755378 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_42769193807701 : Nat.Prime 42769193807701 := by
  apply lucas_primality 42769193807701 (2 : ZMod 42769193807701)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 2), (53, 1), (298876267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 2), (53, 1), (298876267, 1)] : List FactorBlock).map factorBlockValue).prod) = 42769193807701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_53
      · exact prime_fortyOneAM_298876267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42769193807701) ^ 21384596903850 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 42769193807701) ^ 14256397935900 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 42769193807701) ^ 8553838761540 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 42769193807701) ^ 806965920900 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 42769193807701) ^ 143100 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_45485416365373 : Nat.Prime 45485416365373 := by
  apply lucas_primality 45485416365373 (2 : ZMod 45485416365373)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (66499146733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (66499146733, 1)] : List FactorBlock).map factorBlockValue).prod) = 45485416365373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_66499146733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45485416365373) ^ 22742708182686 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 45485416365373) ^ 15161805455124 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 45485416365373) ^ 2393969282388 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 45485416365373) ^ 684 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_66605060096137 : Nat.Prime 66605060096137 := by
  apply lucas_primality 66605060096137 (5 : ZMod 66605060096137)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (19, 1), (48687909427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (19, 1), (48687909427, 1)] : List FactorBlock).map factorBlockValue).prod) = 66605060096137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_48687909427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66605060096137) ^ 33302530048068 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 66605060096137) ^ 22201686698712 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 66605060096137) ^ 3505529478744 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 66605060096137) ^ 1368 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_73957988809921 : Nat.Prime 73957988809921 := by
  apply lucas_primality 73957988809921 (11 : ZMod 73957988809921)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (1087, 1), (70873571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (1087, 1), (70873571, 1)] : List FactorBlock).map factorBlockValue).prod) = 73957988809921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_1087
      · exact prime_fortyOneAM_70873571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 73957988809921) ^ 36978994404960 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 73957988809921) ^ 24652662936640 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 73957988809921) ^ 14791597761984 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 73957988809921) ^ 68038628160 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 73957988809921) ^ 1043520 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_76087802009833 : Nat.Prime 76087802009833 := by
  apply lucas_primality 76087802009833 (5 : ZMod 76087802009833)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (109, 1), (179, 1), (162489113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (109, 1), (179, 1), (162489113, 1)] : List FactorBlock).map factorBlockValue).prod) = 76087802009833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_109
      · exact prime_fortyOneAM_179
      · exact prime_fortyOneAM_162489113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 76087802009833) ^ 38043901004916 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 76087802009833) ^ 25362600669944 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 76087802009833) ^ 698053229448 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 76087802009833) ^ 425071519608 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 76087802009833) ^ 468264 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_90838108578901 : Nat.Prime 90838108578901 := by
  apply lucas_primality 90838108578901 (10 : ZMod 90838108578901)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (17, 1), (19, 1), (23767, 1), (39443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (17, 1), (19, 1), (23767, 1), (39443, 1)] : List FactorBlock).map factorBlockValue).prod) = 90838108578901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_23767
      · exact prime_fortyOneAM_39443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 90838108578901) ^ 45419054289450 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 90838108578901) ^ 30279369526300 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 90838108578901) ^ 18167621715780 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 90838108578901) ^ 5343418151700 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 90838108578901) ^ 4780953083100 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 90838108578901) ^ 3822026700 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 90838108578901) ^ 2303022300 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_92300765767319 : Nat.Prime 92300765767319 := by
  apply lucas_primality 92300765767319 (7 : ZMod 92300765767319)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4463489, 1), (10339531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4463489, 1), (10339531, 1)] : List FactorBlock).map factorBlockValue).prod) = 92300765767319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_4463489
      · exact prime_fortyOneAM_10339531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 92300765767319) ^ 46150382883659 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 92300765767319) ^ 20679062 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 92300765767319) ^ 8926978 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_117085522488097 : Nat.Prime 117085522488097 := by
  apply lucas_primality 117085522488097 (5 : ZMod 117085522488097)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (4153, 1), (293677067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (4153, 1), (293677067, 1)] : List FactorBlock).map factorBlockValue).prod) = 117085522488097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_4153
      · exact prime_fortyOneAM_293677067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 117085522488097) ^ 58542761244048 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 117085522488097) ^ 39028507496032 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 117085522488097) ^ 28192998432 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 117085522488097) ^ 398688 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_168101285719853 : Nat.Prime 168101285719853 := by
  apply lucas_primality 168101285719853 (2 : ZMod 168101285719853)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (331339, 1), (126834817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (331339, 1), (126834817, 1)] : List FactorBlock).map factorBlockValue).prod) = 168101285719853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_331339
      · exact prime_fortyOneAM_126834817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 168101285719853) ^ 84050642859926 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 168101285719853) ^ 507339268 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 168101285719853) ^ 1325356 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_213236298175301 : Nat.Prime 213236298175301 := by
  apply lucas_primality 213236298175301 (3 : ZMod 213236298175301)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (2132362981753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (2132362981753, 1)] : List FactorBlock).map factorBlockValue).prod) = 213236298175301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_2132362981753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 213236298175301) ^ 106618149087650 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 213236298175301) ^ 42647259635060 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 213236298175301) ^ 100 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_237981627128339 : Nat.Prime 237981627128339 := by
  apply lucas_primality 237981627128339 (2 : ZMod 237981627128339)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (633079, 1), (187955711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (633079, 1), (187955711, 1)] : List FactorBlock).map factorBlockValue).prod) = 237981627128339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_633079
      · exact prime_fortyOneAM_187955711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 237981627128339) ^ 118990813564169 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 237981627128339) ^ 375911422 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 237981627128339) ^ 1266158 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_251850697192999 : Nat.Prime 251850697192999 := by
  apply lucas_primality 251850697192999 (3 : ZMod 251850697192999)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (97, 1), (144244385563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (97, 1), (144244385563, 1)] : List FactorBlock).map factorBlockValue).prod) = 251850697192999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_97
      · exact prime_fortyOneAM_144244385563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 251850697192999) ^ 125925348596499 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 251850697192999) ^ 83950232397666 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 251850697192999) ^ 2596398940134 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 251850697192999) ^ 1746 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_295623051014479 : Nat.Prime 295623051014479 := by
  apply lucas_primality 295623051014479 (6 : ZMod 295623051014479)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (199, 1), (22508226817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (199, 1), (22508226817, 1)] : List FactorBlock).map factorBlockValue).prod) = 295623051014479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_199
      · exact prime_fortyOneAM_22508226817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 295623051014479) ^ 147811525507239 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 295623051014479) ^ 98541017004826 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 295623051014479) ^ 26874822819498 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 295623051014479) ^ 1485542969922 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 295623051014479) ^ 13134 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_398610646850761 : Nat.Prime 398610646850761 := by
  apply lucas_primality 398610646850761 (13 : ZMod 398610646850761)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (6961, 1), (477195143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (6961, 1), (477195143, 1)] : List FactorBlock).map factorBlockValue).prod) = 398610646850761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_6961
      · exact prime_fortyOneAM_477195143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 398610646850761) ^ 199305323425380 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (13 : ZMod 398610646850761) ^ 132870215616920 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (13 : ZMod 398610646850761) ^ 79722129370152 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (13 : ZMod 398610646850761) ^ 57263417160 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (13 : ZMod 398610646850761) ^ 835320 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_441303371073883 : Nat.Prime 441303371073883 := by
  apply lucas_primality 441303371073883 (3 : ZMod 441303371073883)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (24516853948549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (24516853948549, 1)] : List FactorBlock).map factorBlockValue).prod) = 441303371073883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_24516853948549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 441303371073883) ^ 220651685536941 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 441303371073883) ^ 147101123691294 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 441303371073883) ^ 18 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_453849529498259 : Nat.Prime 453849529498259 := by
  apply lucas_primality 453849529498259 (2 : ZMod 453849529498259)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (673, 1), (37199, 1), (312563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (673, 1), (37199, 1), (312563, 1)] : List FactorBlock).map factorBlockValue).prod) = 453849529498259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_673
      · exact prime_fortyOneAM_37199
      · exact prime_fortyOneAM_312563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 453849529498259) ^ 226924764749129 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 453849529498259) ^ 15649983775802 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 453849529498259) ^ 674367800146 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 453849529498259) ^ 12200584142 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 453849529498259) ^ 1452025766 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_476640155138723 : Nat.Prime 476640155138723 := by
  apply lucas_primality 476640155138723 (2 : ZMod 476640155138723)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (661, 1), (360544746701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (661, 1), (360544746701, 1)] : List FactorBlock).map factorBlockValue).prod) = 476640155138723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_661
      · exact prime_fortyOneAM_360544746701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 476640155138723) ^ 238320077569361 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 476640155138723) ^ 721089493402 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 476640155138723) ^ 1322 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_893673465963017 : Nat.Prime 893673465963017 := by
  apply lucas_primality 893673465963017 (3 : ZMod 893673465963017)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (337, 1), (8084908681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (337, 1), (8084908681, 1)] : List FactorBlock).map factorBlockValue).prod) = 893673465963017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_41
      · exact prime_fortyOneAM_337
      · exact prime_fortyOneAM_8084908681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 893673465963017) ^ 446836732981508 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 893673465963017) ^ 21796913803976 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 893673465963017) ^ 2651850047368 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 893673465963017) ^ 110536 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1162136792884549 : Nat.Prime 1162136792884549 := by
  apply lucas_primality 1162136792884549 (2 : ZMod 1162136792884549)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (103, 1), (1489, 1), (48573649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (103, 1), (1489, 1), (48573649, 1)] : List FactorBlock).map factorBlockValue).prod) = 1162136792884549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_103
      · exact prime_fortyOneAM_1489
      · exact prime_fortyOneAM_48573649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1162136792884549) ^ 581068396442274 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1162136792884549) ^ 387378930961516 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1162136792884549) ^ 89395137914196 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1162136792884549) ^ 11282881484316 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1162136792884549) ^ 780481392132 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1162136792884549) ^ 23925252 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1325362503021437 : Nat.Prime 1325362503021437 := by
  apply lucas_primality 1325362503021437 (2 : ZMod 1325362503021437)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (30121875068669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (30121875068669, 1)] : List FactorBlock).map factorBlockValue).prod) = 1325362503021437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_30121875068669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1325362503021437) ^ 662681251510718 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1325362503021437) ^ 120487500274676 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1325362503021437) ^ 44 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1346197288565257 : Nat.Prime 1346197288565257 := by
  apply lucas_primality 1346197288565257 (5 : ZMod 1346197288565257)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (241, 1), (25321, 1), (296509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (241, 1), (25321, 1), (296509, 1)] : List FactorBlock).map factorBlockValue).prod) = 1346197288565257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_31
      · exact prime_fortyOneAM_241
      · exact prime_fortyOneAM_25321
      · exact prime_fortyOneAM_296509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1346197288565257) ^ 673098644282628 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1346197288565257) ^ 448732429521752 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1346197288565257) ^ 43425718985976 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1346197288565257) ^ 5585880865416 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1346197288565257) ^ 53165249736 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1346197288565257) ^ 4540156584 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1551806196378491 : Nat.Prime 1551806196378491 := by
  apply lucas_primality 1551806196378491 (7 : ZMod 1551806196378491)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (19, 1), (29, 1), (89, 1), (243417907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (19, 1), (29, 1), (89, 1), (243417907, 1)] : List FactorBlock).map factorBlockValue).prod) = 1551806196378491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_89
      · exact prime_fortyOneAM_243417907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1551806196378491) ^ 775903098189245 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1551806196378491) ^ 310361239275698 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1551806196378491) ^ 119369707413730 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1551806196378491) ^ 81674010335710 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1551806196378491) ^ 53510558495810 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1551806196378491) ^ 17436024678410 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1551806196378491) ^ 6375070 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_41
      · exact prime_fortyOneAM_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1690491921252391 : Nat.Prime 1690491921252391 := by
  apply lucas_primality 1690491921252391 (6 : ZMod 1690491921252391)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (149, 1), (159631, 1), (789709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (149, 1), (159631, 1), (789709, 1)] : List FactorBlock).map factorBlockValue).prod) = 1690491921252391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_149
      · exact prime_fortyOneAM_159631
      · exact prime_fortyOneAM_789709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1690491921252391) ^ 845245960626195 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1690491921252391) ^ 563497307084130 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1690491921252391) ^ 338098384250478 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1690491921252391) ^ 11345583364110 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1690491921252391) ^ 10589997690 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1690491921252391) ^ 2140651710 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1809966632675527 : Nat.Prime 1809966632675527 := by
  apply lucas_primality 1809966632675527 (7 : ZMod 1809966632675527)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (785431, 1), (9847969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (785431, 1), (9847969, 1)] : List FactorBlock).map factorBlockValue).prod) = 1809966632675527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_785431
      · exact prime_fortyOneAM_9847969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1809966632675527) ^ 904983316337763 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1809966632675527) ^ 603322210891842 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1809966632675527) ^ 139228202513502 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1809966632675527) ^ 2304424746 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1809966632675527) ^ 183790854 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1902893672332357 : Nat.Prime 1902893672332357 := by
  apply lucas_primality 1902893672332357 (2 : ZMod 1902893672332357)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (599, 1), (24066546167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (599, 1), (24066546167, 1)] : List FactorBlock).map factorBlockValue).prod) = 1902893672332357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_599
      · exact prime_fortyOneAM_24066546167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1902893672332357) ^ 951446836166178 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1902893672332357) ^ 634297890777452 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1902893672332357) ^ 172990333848396 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1902893672332357) ^ 3176784094044 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1902893672332357) ^ 79068 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_2288055551167361 : Nat.Prime 2288055551167361 := by
  apply lucas_primality 2288055551167361 (3 : ZMod 2288055551167361)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (13, 1), (73, 1), (11867, 1), (317453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (13, 1), (73, 1), (11867, 1), (317453, 1)] : List FactorBlock).map factorBlockValue).prod) = 2288055551167361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_73
      · exact prime_fortyOneAM_11867
      · exact prime_fortyOneAM_317453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2288055551167361) ^ 1144027775583680 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2288055551167361) ^ 457611110233472 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2288055551167361) ^ 176004273166720 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2288055551167361) ^ 31343226728320 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2288055551167361) ^ 192808254080 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2288055551167361) ^ 7207541120 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_2516595694244803 : Nat.Prime 2516595694244803 := by
  apply lucas_primality 2516595694244803 (2 : ZMod 2516595694244803)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7621, 1), (18345475909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7621, 1), (18345475909, 1)] : List FactorBlock).map factorBlockValue).prod) = 2516595694244803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_7621
      · exact prime_fortyOneAM_18345475909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2516595694244803) ^ 1258297847122401 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2516595694244803) ^ 838865231414934 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2516595694244803) ^ 330218566362 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2516595694244803) ^ 137178 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_5538045946039141 : Nat.Prime 5538045946039141 := by
  apply lucas_primality 5538045946039141 (11 : ZMod 5538045946039141)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (92300765767319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (92300765767319, 1)] : List FactorBlock).map factorBlockValue).prod) = 5538045946039141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_92300765767319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 5538045946039141) ^ 2769022973019570 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 5538045946039141) ^ 1846015315346380 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 5538045946039141) ^ 1107609189207828 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 5538045946039141) ^ 60 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_9048561206416337 : Nat.Prime 9048561206416337 := by
  apply lucas_primality 9048561206416337 (3 : ZMod 9048561206416337)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (2393, 1), (8447, 1), (2543441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (2393, 1), (8447, 1), (2543441, 1)] : List FactorBlock).map factorBlockValue).prod) = 9048561206416337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_2393
      · exact prime_fortyOneAM_8447
      · exact prime_fortyOneAM_2543441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9048561206416337) ^ 4524280603208168 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 9048561206416337) ^ 822596473310576 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 9048561206416337) ^ 3781262518352 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 9048561206416337) ^ 1071215959088 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 9048561206416337) ^ 3557606096 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_13698015089224237 : Nat.Prime 13698015089224237 := by
  apply lucas_primality 13698015089224237 (5 : ZMod 13698015089224237)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (29, 1), (359, 1), (877, 1), (1289, 1), (4217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (29, 1), (359, 1), (877, 1), (1289, 1), (4217, 1)] : List FactorBlock).map factorBlockValue).prod) = 13698015089224237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_359
      · exact prime_fortyOneAM_877
      · exact prime_fortyOneAM_1289
      · exact prime_fortyOneAM_4217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 13698015089224237) ^ 6849007544612118 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 13698015089224237) ^ 4566005029741412 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 13698015089224237) ^ 595565873444532 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 13698015089224237) ^ 472345347904284 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 13698015089224237) ^ 38156030889204 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 13698015089224237) ^ 15619173419868 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 13698015089224237) ^ 10626854219724 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 13698015089224237) ^ 3248284346508 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_14993352319506247 : Nat.Prime 14993352319506247 := by
  apply lucas_primality 14993352319506247 (3 : ZMod 14993352319506247)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (223, 1), (2089, 1), (4391, 1), (19391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (223, 1), (2089, 1), (4391, 1), (19391, 1)] : List FactorBlock).map factorBlockValue).prod) = 14993352319506247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_223
      · exact prime_fortyOneAM_2089
      · exact prime_fortyOneAM_4391
      · exact prime_fortyOneAM_19391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14993352319506247) ^ 7496676159753123 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 14993352319506247) ^ 4997784106502082 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 14993352319506247) ^ 2141907474215178 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 14993352319506247) ^ 67234763764602 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 14993352319506247) ^ 7177286893014 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 14993352319506247) ^ 3414564408906 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 14993352319506247) ^ 773211918906 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_25065826015695097 : Nat.Prime 25065826015695097 := by
  apply lucas_primality 25065826015695097 (5 : ZMod 25065826015695097)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (157, 1), (6652289282297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (157, 1), (6652289282297, 1)] : List FactorBlock).map factorBlockValue).prod) = 25065826015695097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_157
      · exact prime_fortyOneAM_6652289282297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 25065826015695097) ^ 12532913007847548 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 25065826015695097) ^ 8355275338565032 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 25065826015695097) ^ 159654942775128 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 25065826015695097) ^ 3768 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_54291367238498023 : Nat.Prime 54291367238498023 := by
  apply lucas_primality 54291367238498023 (6 : ZMod 54291367238498023)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9048561206416337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9048561206416337, 1)] : List FactorBlock).map factorBlockValue).prod) = 54291367238498023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_9048561206416337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 54291367238498023) ^ 27145683619249011 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 54291367238498023) ^ 18097122412832674 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 54291367238498023) ^ 6 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_249646472141438849 : Nat.Prime 249646472141438849 := by
  apply lucas_primality 249646472141438849 (3 : ZMod 249646472141438849)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (61, 1), (2897, 1), (1576663789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (61, 1), (2897, 1), (1576663789, 1)] : List FactorBlock).map factorBlockValue).prod) = 249646472141438849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_61
      · exact prime_fortyOneAM_2897
      · exact prime_fortyOneAM_1576663789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 249646472141438849) ^ 124823236070719424 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 249646472141438849) ^ 35663781734491264 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 249646472141438849) ^ 4092565117072768 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 249646472141438849) ^ 86174136051584 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 249646472141438849) ^ 158338432 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_253883792799835741 : Nat.Prime 253883792799835741 := by
  apply lucas_primality 253883792799835741 (10 : ZMod 253883792799835741)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (47, 1), (227, 1), (313, 1), (1129, 1), (374111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (47, 1), (227, 1), (313, 1), (1129, 1), (374111, 1)] : List FactorBlock).map factorBlockValue).prod) = 253883792799835741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_47
      · exact prime_fortyOneAM_227
      · exact prime_fortyOneAM_313
      · exact prime_fortyOneAM_1129
      · exact prime_fortyOneAM_374111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 253883792799835741) ^ 126941896399917870 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 253883792799835741) ^ 84627930933278580 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 253883792799835741) ^ 50776758559967148 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 253883792799835741) ^ 5401782825528420 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 253883792799835741) ^ 1118430805285620 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 253883792799835741) ^ 811130328433980 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 253883792799835741) ^ 224874927192060 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 253883792799835741) ^ 678632258340 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_269155507944894293 : Nat.Prime 269155507944894293 := by
  apply lucas_primality 269155507944894293 (2 : ZMod 269155507944894293)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (137, 1), (16189, 1), (30339099761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (137, 1), (16189, 1), (30339099761, 1)] : List FactorBlock).map factorBlockValue).prod) = 269155507944894293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_137
      · exact prime_fortyOneAM_16189
      · exact prime_fortyOneAM_30339099761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 269155507944894293) ^ 134577753972447146 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 269155507944894293) ^ 1964638744123316 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 269155507944894293) ^ 16625826669028 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 269155507944894293) ^ 8871572 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_272415889211090231 : Nat.Prime 272415889211090231 := by
  apply lucas_primality 272415889211090231 (34 : ZMod 272415889211090231)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (476243, 1), (57201027461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (476243, 1), (57201027461, 1)] : List FactorBlock).map factorBlockValue).prod) = 272415889211090231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_476243
      · exact prime_fortyOneAM_57201027461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (34 : ZMod 272415889211090231) ^ 136207944605545115 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (34 : ZMod 272415889211090231) ^ 54483177842218046 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (34 : ZMod 272415889211090231) ^ 572010274610 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (34 : ZMod 272415889211090231) ^ 4762430 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_367750818909779951 : Nat.Prime 367750818909779951 := by
  apply lucas_primality 367750818909779951 (7 : ZMod 367750818909779951)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (23, 1), (6698767, 1), (47737639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (23, 1), (6698767, 1), (47737639, 1)] : List FactorBlock).map factorBlockValue).prod) = 367750818909779951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_6698767
      · exact prime_fortyOneAM_47737639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 367750818909779951) ^ 183875409454889975 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 367750818909779951) ^ 73550163781955990 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 367750818909779951) ^ 15989166039555650 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 367750818909779951) ^ 54898284850 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 367750818909779951) ^ 7703582050 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_393283281186609733 : Nat.Prime 393283281186609733 := by
  apply lucas_primality 393283281186609733 (2 : ZMod 393283281186609733)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 7), (31, 1), (1450223760589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 7), (31, 1), (1450223760589, 1)] : List FactorBlock).map factorBlockValue).prod) = 393283281186609733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_31
      · exact prime_fortyOneAM_1450223760589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 393283281186609733) ^ 196641640593304866 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 393283281186609733) ^ 131094427062203244 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 393283281186609733) ^ 12686557457632572 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 393283281186609733) ^ 271188 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_554416845428909831 : Nat.Prime 554416845428909831 := by
  apply lucas_primality 554416845428909831 (7 : ZMod 554416845428909831)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (467, 1), (543689, 1), (218357941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (467, 1), (543689, 1), (218357941, 1)] : List FactorBlock).map factorBlockValue).prod) = 554416845428909831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_467
      · exact prime_fortyOneAM_543689
      · exact prime_fortyOneAM_218357941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 554416845428909831) ^ 277208422714454915 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 554416845428909831) ^ 110883369085781966 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 554416845428909831) ^ 1187188105843490 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 554416845428909831) ^ 1019731584470 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 554416845428909831) ^ 2539027630 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_61717
      · exact prime_fortyOneAM_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1088494281542954707 : Nat.Prime 1088494281542954707 := by
  apply lucas_primality 1088494281542954707 (2 : ZMod 1088494281542954707)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (893673465963017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (893673465963017, 1)] : List FactorBlock).map factorBlockValue).prod) = 1088494281542954707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_893673465963017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1088494281542954707) ^ 544247140771477353 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1088494281542954707) ^ 362831427180984902 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1088494281542954707) ^ 155499183077564958 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1088494281542954707) ^ 37534285570446714 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1088494281542954707) ^ 1218 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1523302756799014447 : Nat.Prime 1523302756799014447 := by
  apply lucas_primality 1523302756799014447 (3 : ZMod 1523302756799014447)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (253883792799835741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (253883792799835741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1523302756799014447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_253883792799835741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1523302756799014447) ^ 761651378399507223 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1523302756799014447) ^ 507767585599671482 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1523302756799014447) ^ 6 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_3620330232355834061 : Nat.Prime 3620330232355834061 := by
  apply lucas_primality 3620330232355834061 (2 : ZMod 3620330232355834061)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (19, 1), (2153, 1), (8501, 1), (74362247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (19, 1), (2153, 1), (8501, 1), (74362247, 1)] : List FactorBlock).map factorBlockValue).prod) = 3620330232355834061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_2153
      · exact prime_fortyOneAM_8501
      · exact prime_fortyOneAM_74362247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3620330232355834061) ^ 1810165116177917030 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3620330232355834061) ^ 724066046471166812 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3620330232355834061) ^ 517190033193690580 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3620330232355834061) ^ 190543696439780740 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3620330232355834061) ^ 1681528208247020 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3620330232355834061) ^ 425871101324060 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3620330232355834061) ^ 48685056980 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_10214829223965708443 : Nat.Prime 10214829223965708443 := by
  apply lucas_primality 10214829223965708443 (2 : ZMod 10214829223965708443)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (313, 1), (10976507, 1), (1486594831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (313, 1), (10976507, 1), (1486594831, 1)] : List FactorBlock).map factorBlockValue).prod) = 10214829223965708443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_313
      · exact prime_fortyOneAM_10976507
      · exact prime_fortyOneAM_1486594831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10214829223965708443) ^ 5107414611982854221 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10214829223965708443) ^ 32635237137270634 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10214829223965708443) ^ 930608364206 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10214829223965708443) ^ 6871293382 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_13047586499150352329 : Nat.Prime 13047586499150352329 := by
  apply lucas_primality 13047586499150352329 (3 : ZMod 13047586499150352329)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1051, 1), (1551806196378491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1051, 1), (1551806196378491, 1)] : List FactorBlock).map factorBlockValue).prod) = 13047586499150352329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_1051
      · exact prime_fortyOneAM_1551806196378491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 13047586499150352329) ^ 6523793249575176164 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 13047586499150352329) ^ 12414449571027928 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 13047586499150352329) ^ 8408 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_15518395153927508599 : Nat.Prime 15518395153927508599 := by
  apply lucas_primality 15518395153927508599 (6 : ZMod 15518395153927508599)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (9652759, 1), (12759239747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (9652759, 1), (12759239747, 1)] : List FactorBlock).map factorBlockValue).prod) = 15518395153927508599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_9652759
      · exact prime_fortyOneAM_12759239747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 15518395153927508599) ^ 7759197576963754299 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 15518395153927508599) ^ 5172798384642502866 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 15518395153927508599) ^ 2216913593418215514 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 15518395153927508599) ^ 1607664208122 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (6 : ZMod 15518395153927508599) ^ 1216247634 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_59631317757104430761 : Nat.Prime 59631317757104430761 := by
  apply lucas_primality 59631317757104430761 (3 : ZMod 59631317757104430761)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (5381, 1), (14243681, 1), (19450429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (5381, 1), (14243681, 1), (19450429, 1)] : List FactorBlock).map factorBlockValue).prod) = 59631317757104430761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_5381
      · exact prime_fortyOneAM_14243681
      · exact prime_fortyOneAM_19450429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 59631317757104430761) ^ 29815658878552215380 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 59631317757104430761) ^ 11926263551420886152 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 59631317757104430761) ^ 11081828239565960 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 59631317757104430761) ^ 4186510337960 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 59631317757104430761) ^ 3065809898440 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_92096753199254438471 : Nat.Prime 92096753199254438471 := by
  apply lucas_primality 92096753199254438471 (7 : ZMod 92096753199254438471)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (161267, 1), (1005241, 1), (5164591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (161267, 1), (1005241, 1), (5164591, 1)] : List FactorBlock).map factorBlockValue).prod) = 92096753199254438471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_161267
      · exact prime_fortyOneAM_1005241
      · exact prime_fortyOneAM_5164591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 92096753199254438471) ^ 46048376599627219235 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 92096753199254438471) ^ 18419350639850887694 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 92096753199254438471) ^ 8372432109023130770 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 92096753199254438471) ^ 571082448357410 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 92096753199254438471) ^ 91616590647670 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 92096753199254438471) ^ 17832342038170 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_119174730659429860771 : Nat.Prime 119174730659429860771 := by
  apply lucas_primality 119174730659429860771 (3 : ZMod 119174730659429860771)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (206182633, 1), (19266855623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (206182633, 1), (19266855623, 1)] : List FactorBlock).map factorBlockValue).prod) = 119174730659429860771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_206182633
      · exact prime_fortyOneAM_19266855623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 119174730659429860771) ^ 59587365329714930385 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 119174730659429860771) ^ 39724910219809953590 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 119174730659429860771) ^ 23834946131885972154 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 119174730659429860771) ^ 578005668690 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 119174730659429860771) ^ 6185478990 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_171355180240039693759 : Nat.Prime 171355180240039693759 := by
  apply lucas_primality 171355180240039693759 (3 : ZMod 171355180240039693759)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (131, 1), (158419, 1), (196593604091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (131, 1), (158419, 1), (196593604091, 1)] : List FactorBlock).map factorBlockValue).prod) = 171355180240039693759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_131
      · exact prime_fortyOneAM_158419
      · exact prime_fortyOneAM_196593604091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 171355180240039693759) ^ 85677590120019846879 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 171355180240039693759) ^ 57118393413346564586 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 171355180240039693759) ^ 24479311462862813394 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 171355180240039693759) ^ 1308054810992669418 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 171355180240039693759) ^ 1081658009708682 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 171355180240039693759) ^ 871621338 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_242435042859187229351 : Nat.Prime 242435042859187229351 := by
  apply lucas_primality 242435042859187229351 (11 : ZMod 242435042859187229351)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (2917, 1), (435109, 1), (293864783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (2917, 1), (435109, 1), (293864783, 1)] : List FactorBlock).map factorBlockValue).prod) = 242435042859187229351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_2917
      · exact prime_fortyOneAM_435109
      · exact prime_fortyOneAM_293864783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 242435042859187229351) ^ 121217521429593614675 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 242435042859187229351) ^ 48487008571837445870 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 242435042859187229351) ^ 18648849450706709950 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 242435042859187229351) ^ 83111087713125550 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 242435042859187229351) ^ 557182321807150 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 242435042859187229351) ^ 824988419450 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_506258606351371954499 : Nat.Prime 506258606351371954499 := by
  apply lucas_primality 506258606351371954499 (2 : ZMod 506258606351371954499)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (101, 1), (11681, 1), (19505107163239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (101, 1), (11681, 1), (19505107163239, 1)] : List FactorBlock).map factorBlockValue).prod) = 506258606351371954499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_101
      · exact prime_fortyOneAM_11681
      · exact prime_fortyOneAM_19505107163239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 506258606351371954499) ^ 253129303175685977249 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 506258606351371954499) ^ 46023509668306541318 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 506258606351371954499) ^ 5012461449023484698 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 506258606351371954499) ^ 43340348116717058 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 506258606351371954499) ^ 25955182 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_624586935274748070337 : Nat.Prime 624586935274748070337 := by
  apply lucas_primality 624586935274748070337 (7 : ZMod 624586935274748070337)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (1721, 1), (48679, 1), (12943385729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (1721, 1), (48679, 1), (12943385729, 1)] : List FactorBlock).map factorBlockValue).prod) = 624586935274748070337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_1721
      · exact prime_fortyOneAM_48679
      · exact prime_fortyOneAM_12943385729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 624586935274748070337) ^ 312293467637374035168 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 624586935274748070337) ^ 208195645091582690112 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 624586935274748070337) ^ 362920938567546816 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 624586935274748070337) ^ 12830726499614784 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 624586935274748070337) ^ 48255297984 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_993061107046487393611 : Nat.Prime 993061107046487393611 := by
  apply lucas_primality 993061107046487393611 (2 : ZMod 993061107046487393611)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (61, 1), (577, 1), (7057, 1), (10847, 1), (12286249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (61, 1), (577, 1), (7057, 1), (10847, 1), (12286249, 1)] : List FactorBlock).map factorBlockValue).prod) = 993061107046487393611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_61
      · exact prime_fortyOneAM_577
      · exact prime_fortyOneAM_7057
      · exact prime_fortyOneAM_10847
      · exact prime_fortyOneAM_12286249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 993061107046487393611) ^ 496530553523243696805 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 993061107046487393611) ^ 331020369015495797870 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 993061107046487393611) ^ 198612221409297478722 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 993061107046487393611) ^ 16279690279450613010 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 993061107046487393611) ^ 1721076442021641930 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 993061107046487393611) ^ 140720009500706730 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 993061107046487393611) ^ 91551683142480630 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 993061107046487393611) ^ 80827037368890 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_107
      · exact prime_fortyOneAM_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_2631099150712756233281 : Nat.Prime 2631099150712756233281 := by
  apply lucas_primality 2631099150712756233281 (3 : ZMod 2631099150712756233281)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (67, 1), (199, 1), (5081, 1), (38183, 1), (3178631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (67, 1), (199, 1), (5081, 1), (38183, 1), (3178631, 1)] : List FactorBlock).map factorBlockValue).prod) = 2631099150712756233281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_67
      · exact prime_fortyOneAM_199
      · exact prime_fortyOneAM_5081
      · exact prime_fortyOneAM_38183
      · exact prime_fortyOneAM_3178631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2631099150712756233281) ^ 1315549575356378116640 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2631099150712756233281) ^ 526219830142551246656 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2631099150712756233281) ^ 39270136577802331840 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2631099150712756233281) ^ 13221603772425910720 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2631099150712756233281) ^ 517830968453602880 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2631099150712756233281) ^ 68907606807028160 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2631099150712756233281) ^ 827746017298880 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_2773245013380264502883 : Nat.Prime 2773245013380264502883 := by
  apply lucas_primality 2773245013380264502883 (2 : ZMod 2773245013380264502883)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (7981327, 1), (15793938967453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (7981327, 1), (15793938967453, 1)] : List FactorBlock).map factorBlockValue).prod) = 2773245013380264502883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_7981327
      · exact prime_fortyOneAM_15793938967453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2773245013380264502883) ^ 1386622506690132251441 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2773245013380264502883) ^ 252113183034569500262 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2773245013380264502883) ^ 347466657283966 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2773245013380264502883) ^ 175589194 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_4291120773970962637997 : Nat.Prime 4291120773970962637997 := by
  apply lucas_primality 4291120773970962637997 (2 : ZMod 4291120773970962637997)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2250713, 1), (476640155138723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2250713, 1), (476640155138723, 1)] : List FactorBlock).map factorBlockValue).prod) = 4291120773970962637997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_2250713
      · exact prime_fortyOneAM_476640155138723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4291120773970962637997) ^ 2145560386985481318998 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4291120773970962637997) ^ 1906560620554892 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4291120773970962637997) ^ 9002852 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_4477290904475699490871 : Nat.Prime 4477290904475699490871 := by
  apply lucas_primality 4477290904475699490871 (13 : ZMod 4477290904475699490871)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (3727, 1), (133717, 1), (10326426139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (3727, 1), (133717, 1), (10326426139, 1)] : List FactorBlock).map factorBlockValue).prod) = 4477290904475699490871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_3727
      · exact prime_fortyOneAM_133717
      · exact prime_fortyOneAM_10326426139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 4477290904475699490871) ^ 2238645452237849745435 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (13 : ZMod 4477290904475699490871) ^ 1492430301491899830290 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (13 : ZMod 4477290904475699490871) ^ 895458180895139898174 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (13 : ZMod 4477290904475699490871) ^ 154389341533644810030 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (13 : ZMod 4477290904475699490871) ^ 1201312289904936810 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (13 : ZMod 4477290904475699490871) ^ 33483333491446110 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (13 : ZMod 4477290904475699490871) ^ 433576035330 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_5187294398727270496003 : Nat.Prime 5187294398727270496003 := by
  apply lucas_primality 5187294398727270496003 (3 : ZMod 5187294398727270496003)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (353, 1), (43291, 1), (278689935443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (353, 1), (43291, 1), (278689935443, 1)] : List FactorBlock).map factorBlockValue).prod) = 5187294398727270496003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_353
      · exact prime_fortyOneAM_43291
      · exact prime_fortyOneAM_278689935443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5187294398727270496003) ^ 2593647199363635248001 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5187294398727270496003) ^ 1729098132909090165334 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5187294398727270496003) ^ 741042056961038642286 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5187294398727270496003) ^ 178872220645767948138 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5187294398727270496003) ^ 14694884982230228034 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5187294398727270496003) ^ 119823852503459622 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5187294398727270496003) ^ 18613138614 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_9147622809471831479569 : Nat.Prime 9147622809471831479569 := by
  apply lucas_primality 9147622809471831479569 (7 : ZMod 9147622809471831479569)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7603, 1), (25065826015695097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7603, 1), (25065826015695097, 1)] : List FactorBlock).map factorBlockValue).prod) = 9147622809471831479569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_7603
      · exact prime_fortyOneAM_25065826015695097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 9147622809471831479569) ^ 4573811404735915739784 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 9147622809471831479569) ^ 3049207603157277159856 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 9147622809471831479569) ^ 1203159648753364656 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 9147622809471831479569) ^ 364944 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_11316440304490118260471 : Nat.Prime 11316440304490118260471 := by
  apply lucas_primality 11316440304490118260471 (7 : ZMod 11316440304490118260471)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (127, 1), (251, 1), (1690491921252391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (127, 1), (251, 1), (1690491921252391, 1)] : List FactorBlock).map factorBlockValue).prod) = 11316440304490118260471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_127
      · exact prime_fortyOneAM_251
      · exact prime_fortyOneAM_1690491921252391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11316440304490118260471) ^ 5658220152245059130235 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 11316440304490118260471) ^ 3772146768163372753490 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 11316440304490118260471) ^ 2263288060898023652094 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 11316440304490118260471) ^ 1616634329212874037210 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 11316440304490118260471) ^ 89105829169213529610 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 11316440304490118260471) ^ 45085419539801267970 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 11316440304490118260471) ^ 6694170 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_12976855708430057191067 : Nat.Prime 12976855708430057191067 := by
  apply lucas_primality 12976855708430057191067 (2 : ZMod 12976855708430057191067)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (107, 1), (2897, 1), (1902893672332357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (107, 1), (2897, 1), (1902893672332357, 1)] : List FactorBlock).map factorBlockValue).prod) = 12976855708430057191067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_107
      · exact prime_fortyOneAM_2897
      · exact prime_fortyOneAM_1902893672332357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12976855708430057191067) ^ 6488427854215028595533 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12976855708430057191067) ^ 1179714155311823381006 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12976855708430057191067) ^ 121279025312430441038 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12976855708430057191067) ^ 4479411704670368378 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12976855708430057191067) ^ 6819538 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_14236331146337109770801 : Nat.Prime 14236331146337109770801 := by
  apply lucas_primality 14236331146337109770801 (3 : ZMod 14236331146337109770801)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (7, 1), (109, 1), (228611, 1), (204040523339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (7, 1), (109, 1), (228611, 1), (204040523339, 1)] : List FactorBlock).map factorBlockValue).prod) = 14236331146337109770801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_109
      · exact prime_fortyOneAM_228611
      · exact prime_fortyOneAM_204040523339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14236331146337109770801) ^ 7118165573168554885400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 14236331146337109770801) ^ 2847266229267421954160 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 14236331146337109770801) ^ 2033761592333872824400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 14236331146337109770801) ^ 130608542626945961200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 14236331146337109770801) ^ 62273167723062800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 14236331146337109770801) ^ 69772077200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_31969639094256705149237 : Nat.Prime 31969639094256705149237 := by
  apply lucas_primality 31969639094256705149237 (2 : ZMod 31969639094256705149237)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29339, 1), (272415889211090231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29339, 1), (272415889211090231, 1)] : List FactorBlock).map factorBlockValue).prod) = 31969639094256705149237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_29339
      · exact prime_fortyOneAM_272415889211090231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31969639094256705149237) ^ 15984819547128352574618 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 31969639094256705149237) ^ 1089663556844360924 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 31969639094256705149237) ^ 117356 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_44961452785655980862597 : Nat.Prime 44961452785655980862597 := by
  apply lucas_primality 44961452785655980862597 (2 : ZMod 44961452785655980862597)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (11, 1), (271, 1), (5471, 1), (14065512902851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (11, 1), (271, 1), (5471, 1), (14065512902851, 1)] : List FactorBlock).map factorBlockValue).prod) = 44961452785655980862597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_271
      · exact prime_fortyOneAM_5471
      · exact prime_fortyOneAM_14065512902851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44961452785655980862597) ^ 22480726392827990431298 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 44961452785655980862597) ^ 6423064683665140123228 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 44961452785655980862597) ^ 4087404798695998260236 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 44961452785655980862597) ^ 165909419873269302076 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 44961452785655980862597) ^ 8218141616826170876 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 44961452785655980862597) ^ 3196573996 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_107035713019972117570867 : Nat.Prime 107035713019972117570867 := by
  apply lucas_primality 107035713019972117570867 (2 : ZMod 107035713019972117570867)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 2), (23, 1), (179, 1), (14993352319506247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 2), (23, 1), (179, 1), (14993352319506247, 1)] : List FactorBlock).map factorBlockValue).prod) = 107035713019972117570867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_179
      · exact prime_fortyOneAM_14993352319506247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 107035713019972117570867) ^ 53517856509986058785433 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 107035713019972117570867) ^ 35678571006657372523622 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 107035713019972117570867) ^ 6296218412939536327698 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 107035713019972117570867) ^ 4653726653042265981342 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 107035713019972117570867) ^ 597964877206548142854 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 107035713019972117570867) ^ 7138878 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_161863512122215772529839 : Nat.Prime 161863512122215772529839 := by
  apply lucas_primality 161863512122215772529839 (23 : ZMod 161863512122215772529839)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10099, 1), (156671, 1), (430979, 1), (118685009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10099, 1), (156671, 1), (430979, 1), (118685009, 1)] : List FactorBlock).map factorBlockValue).prod) = 161863512122215772529839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_10099
      · exact prime_fortyOneAM_156671
      · exact prime_fortyOneAM_430979
      · exact prime_fortyOneAM_118685009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 161863512122215772529839) ^ 80931756061107886264919 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (23 : ZMod 161863512122215772529839) ^ 16027677207863726362 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (23 : ZMod 161863512122215772529839) ^ 1033142777681994578 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (23 : ZMod 161863512122215772529839) ^ 375571691711697722 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (23 : ZMod 161863512122215772529839) ^ 1363807556539982 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_340223074022037094262573 : Nat.Prime 340223074022037094262573 := by
  apply lucas_primality 340223074022037094262573 (3 : ZMod 340223074022037094262573)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (19661, 1), (393283281186609733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (19661, 1), (393283281186609733, 1)] : List FactorBlock).map factorBlockValue).prod) = 340223074022037094262573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_19661
      · exact prime_fortyOneAM_393283281186609733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 340223074022037094262573) ^ 170111537011018547131286 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 340223074022037094262573) ^ 30929370365639735842052 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 340223074022037094262573) ^ 17304464372210828252 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 340223074022037094262573) ^ 865084 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_450307887557278742595647 : Nat.Prime 450307887557278742595647 := by
  apply lucas_primality 450307887557278742595647 (7 : ZMod 450307887557278742595647)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (15977771959, 1), (2013099773471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (15977771959, 1), (2013099773471, 1)] : List FactorBlock).map factorBlockValue).prod) = 450307887557278742595647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_15977771959
      · exact prime_fortyOneAM_2013099773471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 450307887557278742595647) ^ 225153943778639371297823 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 450307887557278742595647) ^ 64329698222468391799378 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 450307887557278742595647) ^ 28183396828594 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 450307887557278742595647) ^ 223688807426 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_520626628518508275258749 : Nat.Prime 520626628518508275258749 := by
  apply lucas_primality 520626628518508275258749 (2 : ZMod 520626628518508275258749)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (47, 1), (367, 1), (379, 1), (1809966632675527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (47, 1), (367, 1), (379, 1), (1809966632675527, 1)] : List FactorBlock).map factorBlockValue).prod) = 520626628518508275258749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_47
      · exact prime_fortyOneAM_367
      · exact prime_fortyOneAM_379
      · exact prime_fortyOneAM_1809966632675527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 520626628518508275258749) ^ 260313314259254137629374 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 520626628518508275258749) ^ 47329693501682570478068 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 520626628518508275258749) ^ 11077162308904431388484 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 520626628518508275258749) ^ 1418601167625363147844 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 520626628518508275258749) ^ 1373685035668887269812 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 520626628518508275258749) ^ 287644324 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_626994467057505018341299 : Nat.Prime 626994467057505018341299 := by
  apply lucas_primality 626994467057505018341299 (2 : ZMod 626994467057505018341299)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (12653, 1), (509659, 1), (113319125603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (12653, 1), (509659, 1), (113319125603, 1)] : List FactorBlock).map factorBlockValue).prod) = 626994467057505018341299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_12653
      · exact prime_fortyOneAM_509659
      · exact prime_fortyOneAM_113319125603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 626994467057505018341299) ^ 313497233528752509170649 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 626994467057505018341299) ^ 208998155685835006113766 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 626994467057505018341299) ^ 56999497005227728940118 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 626994467057505018341299) ^ 48230343619808078333946 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 626994467057505018341299) ^ 49553028298230065466 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 626994467057505018341299) ^ 1230223476986583222 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 626994467057505018341299) ^ 5532997750566 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_2328191270327363735252921 : Nat.Prime 2328191270327363735252921 := by
  apply lucas_primality 2328191270327363735252921 (3 : ZMod 2328191270327363735252921)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (4477290904475699490871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (4477290904475699490871, 1)] : List FactorBlock).map factorBlockValue).prod) = 2328191270327363735252921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_4477290904475699490871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2328191270327363735252921) ^ 1164095635163681867626460 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2328191270327363735252921) ^ 465638254065472747050584 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2328191270327363735252921) ^ 179091636179027979634840 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2328191270327363735252921) ^ 520 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_3001234737676658595007481 : Nat.Prime 3001234737676658595007481 := by
  apply lucas_primality 3001234737676658595007481 (3 : ZMod 3001234737676658595007481)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (241, 1), (369629443, 1), (64790751973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (241, 1), (369629443, 1), (64790751973, 1)] : List FactorBlock).map factorBlockValue).prod) = 3001234737676658595007481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_241
      · exact prime_fortyOneAM_369629443
      · exact prime_fortyOneAM_64790751973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3001234737676658595007481) ^ 1500617368838329297503740 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3001234737676658595007481) ^ 600246947535331719001496 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3001234737676658595007481) ^ 230864210590512199615960 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3001234737676658595007481) ^ 12453256172932193340280 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3001234737676658595007481) ^ 8119577037256360 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3001234737676658595007481) ^ 46321961796760 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_4656382540654727470505843 : Nat.Prime 4656382540654727470505843 := by
  apply lucas_primality 4656382540654727470505843 (2 : ZMod 4656382540654727470505843)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2328191270327363735252921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2328191270327363735252921, 1)] : List FactorBlock).map factorBlockValue).prod) = 4656382540654727470505843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_2328191270327363735252921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4656382540654727470505843) ^ 2328191270327363735252921 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4656382540654727470505843) ^ 2 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_8612818452063914884144603 : Nat.Prime 8612818452063914884144603 := by
  apply lucas_primality 8612818452063914884144603 (2 : ZMod 8612818452063914884144603)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (131, 1), (24109, 1), (57527, 1), (65295981319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (131, 1), (24109, 1), (57527, 1), (65295981319, 1)] : List FactorBlock).map factorBlockValue).prod) = 8612818452063914884144603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_131
      · exact prime_fortyOneAM_24109
      · exact prime_fortyOneAM_57527
      · exact prime_fortyOneAM_65295981319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8612818452063914884144603) ^ 4306409226031957442072301 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8612818452063914884144603) ^ 2870939484021304961381534 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8612818452063914884144603) ^ 782983495642174080376782 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8612818452063914884144603) ^ 65746705740945915146142 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8612818452063914884144603) ^ 357244948030358574978 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8612818452063914884144603) ^ 149717844700121940726 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8612818452063914884144603) ^ 131904265439958 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_30543756930192635770614887 : Nat.Prime 30543756930192635770614887 := by
  apply lucas_primality 30543756930192635770614887 (5 : ZMod 30543756930192635770614887)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (28031, 1), (75153751, 1), (659038097873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (28031, 1), (75153751, 1), (659038097873, 1)] : List FactorBlock).map factorBlockValue).prod) = 30543756930192635770614887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_28031
      · exact prime_fortyOneAM_75153751
      · exact prime_fortyOneAM_659038097873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 30543756930192635770614887) ^ 15271878465096317885307443 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 30543756930192635770614887) ^ 2776705175472057797328626 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 30543756930192635770614887) ^ 1089642072355343575706 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 30543756930192635770614887) ^ 406416932272517386 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 30543756930192635770614887) ^ 46345965474182 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_104693179801761799066880833 : Nat.Prime 104693179801761799066880833 := by
  apply lucas_primality 104693179801761799066880833 (5 : ZMod 104693179801761799066880833)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (4937, 1), (9293, 1), (2266133, 1), (5244604007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (4937, 1), (9293, 1), (2266133, 1), (5244604007, 1)] : List FactorBlock).map factorBlockValue).prod) = 104693179801761799066880833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_4937
      · exact prime_fortyOneAM_9293
      · exact prime_fortyOneAM_2266133
      · exact prime_fortyOneAM_5244604007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 104693179801761799066880833) ^ 52346589900880899533440416 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 104693179801761799066880833) ^ 34897726600587266355626944 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 104693179801761799066880833) ^ 21205829410930078806336 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 104693179801761799066880833) ^ 11265810804020423874624 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 104693179801761799066880833) ^ 46199044717040791104 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (5 : ZMod 104693179801761799066880833) ^ 19962075241910976 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_494621859675670540489447201 : Nat.Prime 494621859675670540489447201 := by
  apply lucas_primality 494621859675670540489447201 (7 : ZMod 494621859675670540489447201)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 494621859675670540489447201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_31
      · exact prime_fortyOneAM_37
      · exact prime_fortyOneAM_41
      · exact prime_fortyOneAM_43
      · exact prime_fortyOneAM_47
      · exact prime_fortyOneAM_53
      · exact prime_fortyOneAM_59
      · exact prime_fortyOneAM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 494621859675670540489447201) ^ 247310929837835270244723600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 494621859675670540489447201) ^ 164873953225223513496482400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 494621859675670540489447201) ^ 98924371935134108097889440 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 494621859675670540489447201) ^ 44965623606879140044495200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 494621859675670540489447201) ^ 38047835359666964653034400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 494621859675670540489447201) ^ 29095403510333561205261600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 494621859675670540489447201) ^ 26032729456614238973128800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 494621859675670540489447201) ^ 21505298246768284369106400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 494621859675670540489447201) ^ 17055926195712777258256800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 494621859675670540489447201) ^ 15955543860505501306111200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 494621859675670540489447201) ^ 13368158369612717310525600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 494621859675670540489447201) ^ 12063947796967574158279200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 494621859675670540489447201) ^ 11502833945945826523010400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 494621859675670540489447201) ^ 10523869354801500861477600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 494621859675670540489447201) ^ 9332487918408878122442400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 494621859675670540489447201) ^ 8383421350435093906600800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (7 : ZMod 494621859675670540489447201) ^ 8108555076650336729335200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_550828889184269465545066201 : Nat.Prime 550828889184269465545066201 := by
  apply lucas_primality 550828889184269465545066201 (89 : ZMod 550828889184269465545066201)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 550828889184269465545066201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_31
      · exact prime_fortyOneAM_37
      · exact prime_fortyOneAM_41
      · exact prime_fortyOneAM_43
      · exact prime_fortyOneAM_47
      · exact prime_fortyOneAM_53
      · exact prime_fortyOneAM_59
      · exact prime_fortyOneAM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (89 : ZMod 550828889184269465545066201) ^ 275414444592134732772533100 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 550828889184269465545066201) ^ 183609629728089821848355400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 550828889184269465545066201) ^ 110165777836853893109013240 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 550828889184269465545066201) ^ 78689841312038495077866600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 550828889184269465545066201) ^ 42371453014174574272697400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 550828889184269465545066201) ^ 32401699363780556796768600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 550828889184269465545066201) ^ 28990994167593129765529800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 550828889184269465545066201) ^ 23949082138446498501959400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 550828889184269465545066201) ^ 18994099627043774673967800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 550828889184269465545066201) ^ 17768673844653853727260200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 550828889184269465545066201) ^ 14887267275250526095812600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 550828889184269465545066201) ^ 13434850955713889403538200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 550828889184269465545066201) ^ 12809974167076034082443400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 550828889184269465545066201) ^ 11719763599665307777554600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 550828889184269465545066201) ^ 10392997909137159727265400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 550828889184269465545066201) ^ 9336082867529990941441800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 550828889184269465545066201) ^ 9029981789906056812214200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_692470603545938756685226081 : Nat.Prime 692470603545938756685226081 := by
  apply lucas_primality 692470603545938756685226081 (137 : ZMod 692470603545938756685226081)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 692470603545938756685226081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_31
      · exact prime_fortyOneAM_37
      · exact prime_fortyOneAM_41
      · exact prime_fortyOneAM_43
      · exact prime_fortyOneAM_47
      · exact prime_fortyOneAM_53
      · exact prime_fortyOneAM_59
      · exact prime_fortyOneAM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (137 : ZMod 692470603545938756685226081) ^ 346235301772969378342613040 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (137 : ZMod 692470603545938756685226081) ^ 230823534515312918895075360 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (137 : ZMod 692470603545938756685226081) ^ 138494120709187751337045216 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (137 : ZMod 692470603545938756685226081) ^ 98924371935134108097889440 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (137 : ZMod 692470603545938756685226081) ^ 62951873049630796062293280 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (137 : ZMod 692470603545938756685226081) ^ 53266969503533750514248160 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (137 : ZMod 692470603545938756685226081) ^ 40733564914466985687366240 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (137 : ZMod 692470603545938756685226081) ^ 36445821239259934562380320 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (137 : ZMod 692470603545938756685226081) ^ 30107417545475598116748960 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (137 : ZMod 692470603545938756685226081) ^ 23878296673997888161559520 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (137 : ZMod 692470603545938756685226081) ^ 22337761404707701828555680 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (137 : ZMod 692470603545938756685226081) ^ 18715421717457804234735840 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (137 : ZMod 692470603545938756685226081) ^ 16889526915754603821590880 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (137 : ZMod 692470603545938756685226081) ^ 16103967524324157132214560 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (137 : ZMod 692470603545938756685226081) ^ 14733417096722101206068640 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (137 : ZMod 692470603545938756685226081) ^ 13065483085772429371419360 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (137 : ZMod 692470603545938756685226081) ^ 11736789890609131469241120 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (137 : ZMod 692470603545938756685226081) ^ 11351977107310471421069280 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_807882370803595216132763761 : Nat.Prime 807882370803595216132763761 := by
  apply lucas_primality 807882370803595216132763761 (97 : ZMod 807882370803595216132763761)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 807882370803595216132763761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_31
      · exact prime_fortyOneAM_37
      · exact prime_fortyOneAM_41
      · exact prime_fortyOneAM_43
      · exact prime_fortyOneAM_47
      · exact prime_fortyOneAM_53
      · exact prime_fortyOneAM_59
      · exact prime_fortyOneAM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (97 : ZMod 807882370803595216132763761) ^ 403941185401797608066381880 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (97 : ZMod 807882370803595216132763761) ^ 269294123601198405377587920 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (97 : ZMod 807882370803595216132763761) ^ 161576474160719043226552752 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (97 : ZMod 807882370803595216132763761) ^ 115411767257656459447537680 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (97 : ZMod 807882370803595216132763761) ^ 73443851891235928739342160 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (97 : ZMod 807882370803595216132763761) ^ 62144797754122708933289520 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (97 : ZMod 807882370803595216132763761) ^ 47522492400211483301927280 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (97 : ZMod 807882370803595216132763761) ^ 42520124779136590322777040 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (97 : ZMod 807882370803595216132763761) ^ 35125320469721531136207120 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (97 : ZMod 807882370803595216132763761) ^ 27858012786330869521819440 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (97 : ZMod 807882370803595216132763761) ^ 26060721638825652133314960 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (97 : ZMod 807882370803595216132763761) ^ 21834658670367438273858480 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (97 : ZMod 807882370803595216132763761) ^ 19704448068380371125189360 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (97 : ZMod 807882370803595216132763761) ^ 18787962111711516654250320 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (97 : ZMod 807882370803595216132763761) ^ 17188986612842451407080080 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (97 : ZMod 807882370803595216132763761) ^ 15243063600067834266655920 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (97 : ZMod 807882370803595216132763761) ^ 13692921539043986714114640 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (97 : ZMod 807882370803595216132763761) ^ 13243973291862216657914160 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1127277726702690999255019201 : Nat.Prime 1127277726702690999255019201 := by
  apply lucas_primality 1127277726702690999255019201 (67 : ZMod 1127277726702690999255019201)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1127277726702690999255019201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_31
      · exact prime_fortyOneAM_37
      · exact prime_fortyOneAM_41
      · exact prime_fortyOneAM_47
      · exact prime_fortyOneAM_53
      · exact prime_fortyOneAM_59
      · exact prime_fortyOneAM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 1127277726702690999255019201) ^ 563638863351345499627509600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (67 : ZMod 1127277726702690999255019201) ^ 375759242234230333085006400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (67 : ZMod 1127277726702690999255019201) ^ 225455545340538199851003840 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (67 : ZMod 1127277726702690999255019201) ^ 161039675243241571322145600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (67 : ZMod 1127277726702690999255019201) ^ 102479793336608272659547200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (67 : ZMod 1127277726702690999255019201) ^ 86713671284822384558078400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (67 : ZMod 1127277726702690999255019201) ^ 66310454511922999956177600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (67 : ZMod 1127277726702690999255019201) ^ 59330406668562684171316800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (67 : ZMod 1127277726702690999255019201) ^ 49012075074030043445870400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (67 : ZMod 1127277726702690999255019201) ^ 38871645748368655146724800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (67 : ZMod 1127277726702690999255019201) ^ 36363797635570677395323200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (67 : ZMod 1127277726702690999255019201) ^ 30466965586559216196081600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (67 : ZMod 1127277726702690999255019201) ^ 27494578700065634128171200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (67 : ZMod 1127277726702690999255019201) ^ 23984632483035978707553600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (67 : ZMod 1127277726702690999255019201) ^ 21269391069862094325566400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (67 : ZMod 1127277726702690999255019201) ^ 19106402147503237275508800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (67 : ZMod 1127277726702690999255019201) ^ 18479962732830999987787200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1346470618005992026887939601 : Nat.Prime 1346470618005992026887939601 := by
  apply lucas_primality 1346470618005992026887939601 (89 : ZMod 1346470618005992026887939601)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1346470618005992026887939601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_31
      · exact prime_fortyOneAM_37
      · exact prime_fortyOneAM_41
      · exact prime_fortyOneAM_43
      · exact prime_fortyOneAM_47
      · exact prime_fortyOneAM_53
      · exact prime_fortyOneAM_59
      · exact prime_fortyOneAM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (89 : ZMod 1346470618005992026887939601) ^ 673235309002996013443969800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 1346470618005992026887939601) ^ 448823539335330675629313200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 1346470618005992026887939601) ^ 269294123601198405377587920 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 1346470618005992026887939601) ^ 192352945429427432412562800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 1346470618005992026887939601) ^ 122406419818726547898903600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 1346470618005992026887939601) ^ 103574662923537848222149200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 1346470618005992026887939601) ^ 79204154000352472169878800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 1346470618005992026887939601) ^ 70866874631894317204628400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 1346470618005992026887939601) ^ 58542200782869218560345200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 1346470618005992026887939601) ^ 46430021310551449203032400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 1346470618005992026887939601) ^ 43434536064709420222191600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 1346470618005992026887939601) ^ 36391097783945730456430800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 1346470618005992026887939601) ^ 32840746780633951875315600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 1346470618005992026887939601) ^ 31313270186185861090417200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 1346470618005992026887939601) ^ 28648311021404085678466800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 1346470618005992026887939601) ^ 25405106000113057111093200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 1346470618005992026887939601) ^ 22821535898406644523524400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (89 : ZMod 1346470618005992026887939601) ^ 22073288819770361096523600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1425674772006344499057818401 : Nat.Prime 1425674772006344499057818401 := by
  apply lucas_primality 1425674772006344499057818401 (83 : ZMod 1425674772006344499057818401)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1425674772006344499057818401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_31
      · exact prime_fortyOneAM_37
      · exact prime_fortyOneAM_41
      · exact prime_fortyOneAM_43
      · exact prime_fortyOneAM_47
      · exact prime_fortyOneAM_53
      · exact prime_fortyOneAM_59
      · exact prime_fortyOneAM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 1425674772006344499057818401) ^ 712837386003172249528909200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (83 : ZMod 1425674772006344499057818401) ^ 475224924002114833019272800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (83 : ZMod 1425674772006344499057818401) ^ 285134954401268899811563680 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (83 : ZMod 1425674772006344499057818401) ^ 203667824572334928436831200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (83 : ZMod 1425674772006344499057818401) ^ 129606797455122227187074400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (83 : ZMod 1425674772006344499057818401) ^ 109667290154334192235216800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (83 : ZMod 1425674772006344499057818401) ^ 75035514316123394687253600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (83 : ZMod 1425674772006344499057818401) ^ 61985859652449760828600800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (83 : ZMod 1425674772006344499057818401) ^ 49161199034701534450269600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (83 : ZMod 1425674772006344499057818401) ^ 45989508774398209647026400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (83 : ZMod 1425674772006344499057818401) ^ 38531750594766067542103200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (83 : ZMod 1425674772006344499057818401) ^ 34772555414788890220922400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (83 : ZMod 1425674772006344499057818401) ^ 33155227255961499978088800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (83 : ZMod 1425674772006344499057818401) ^ 30333505787369031894847200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (83 : ZMod 1425674772006344499057818401) ^ 26899524000119707529392800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (83 : ZMod 1425674772006344499057818401) ^ 24163979186548211848437600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (83 : ZMod 1425674772006344499057818401) ^ 23371717573874499984554400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_1731176508864846891713065201 : Nat.Prime 1731176508864846891713065201 := by
  apply lucas_primality 1731176508864846891713065201 (73 : ZMod 1731176508864846891713065201)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1731176508864846891713065201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_31
      · exact prime_fortyOneAM_37
      · exact prime_fortyOneAM_41
      · exact prime_fortyOneAM_43
      · exact prime_fortyOneAM_47
      · exact prime_fortyOneAM_53
      · exact prime_fortyOneAM_59
      · exact prime_fortyOneAM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 1731176508864846891713065201) ^ 865588254432423445856532600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (73 : ZMod 1731176508864846891713065201) ^ 577058836288282297237688400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (73 : ZMod 1731176508864846891713065201) ^ 346235301772969378342613040 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (73 : ZMod 1731176508864846891713065201) ^ 247310929837835270244723600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (73 : ZMod 1731176508864846891713065201) ^ 157379682624076990155733200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (73 : ZMod 1731176508864846891713065201) ^ 133167423758834376285620400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (73 : ZMod 1731176508864846891713065201) ^ 101833912286167464218415600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (73 : ZMod 1731176508864846891713065201) ^ 91114553098149836405950800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (73 : ZMod 1731176508864846891713065201) ^ 75268543863688995291872400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (73 : ZMod 1731176508864846891713065201) ^ 59695741684994720403898800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (73 : ZMod 1731176508864846891713065201) ^ 55844403511769254571389200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (73 : ZMod 1731176508864846891713065201) ^ 46788554293644510586839600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (73 : ZMod 1731176508864846891713065201) ^ 42223817289386509553977200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (73 : ZMod 1731176508864846891713065201) ^ 40259918810810392830536400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (73 : ZMod 1731176508864846891713065201) ^ 36833542741805253015171600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (73 : ZMod 1731176508864846891713065201) ^ 32663707714431073428548400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (73 : ZMod 1731176508864846891713065201) ^ 29341974726522828673102800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (73 : ZMod 1731176508864846891713065201) ^ 28379942768276178552673200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_2019705927008988040331909401 : Nat.Prime 2019705927008988040331909401 := by
  apply lucas_primality 2019705927008988040331909401 (101 : ZMod 2019705927008988040331909401)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2019705927008988040331909401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_31
      · exact prime_fortyOneAM_37
      · exact prime_fortyOneAM_41
      · exact prime_fortyOneAM_43
      · exact prime_fortyOneAM_47
      · exact prime_fortyOneAM_53
      · exact prime_fortyOneAM_59
      · exact prime_fortyOneAM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 2019705927008988040331909401) ^ 1009852963504494020165954700 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (101 : ZMod 2019705927008988040331909401) ^ 673235309002996013443969800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (101 : ZMod 2019705927008988040331909401) ^ 403941185401797608066381880 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (101 : ZMod 2019705927008988040331909401) ^ 288529418144141148618844200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (101 : ZMod 2019705927008988040331909401) ^ 183609629728089821848355400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (101 : ZMod 2019705927008988040331909401) ^ 155361994385306772333223800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (101 : ZMod 2019705927008988040331909401) ^ 118806231000528708254818200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (101 : ZMod 2019705927008988040331909401) ^ 106300311947841475806942600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (101 : ZMod 2019705927008988040331909401) ^ 87813301174303827840517800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (101 : ZMod 2019705927008988040331909401) ^ 69645031965827173804548600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (101 : ZMod 2019705927008988040331909401) ^ 65151804097064130333287400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (101 : ZMod 2019705927008988040331909401) ^ 54586646675918595684646200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (101 : ZMod 2019705927008988040331909401) ^ 49261120170950927812973400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (101 : ZMod 2019705927008988040331909401) ^ 46969905279278791635625800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (101 : ZMod 2019705927008988040331909401) ^ 42972466532106128517700200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (101 : ZMod 2019705927008988040331909401) ^ 38107659000169585666639800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (101 : ZMod 2019705927008988040331909401) ^ 34232303847609966785286600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (101 : ZMod 2019705927008988040331909401) ^ 33109933229655541644785400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_12118235562053928241991456401 : Nat.Prime 12118235562053928241991456401 := by
  apply lucas_primality 12118235562053928241991456401 (113 : ZMod 12118235562053928241991456401)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 12118235562053928241991456401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_31
      · exact prime_fortyOneAM_37
      · exact prime_fortyOneAM_41
      · exact prime_fortyOneAM_43
      · exact prime_fortyOneAM_47
      · exact prime_fortyOneAM_53
      · exact prime_fortyOneAM_59
      · exact prime_fortyOneAM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (113 : ZMod 12118235562053928241991456401) ^ 6059117781026964120995728200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (113 : ZMod 12118235562053928241991456401) ^ 4039411854017976080663818800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (113 : ZMod 12118235562053928241991456401) ^ 2423647112410785648398291280 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (113 : ZMod 12118235562053928241991456401) ^ 1731176508864846891713065200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (113 : ZMod 12118235562053928241991456401) ^ 1101657778368538931090132400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (113 : ZMod 12118235562053928241991456401) ^ 932171966311840633999342800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (113 : ZMod 12118235562053928241991456401) ^ 712837386003172249528909200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (113 : ZMod 12118235562053928241991456401) ^ 637801871687048854841655600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (113 : ZMod 12118235562053928241991456401) ^ 526879807045822967043106800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (113 : ZMod 12118235562053928241991456401) ^ 417870191794963042827291600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (113 : ZMod 12118235562053928241991456401) ^ 390910824582384781999724400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (113 : ZMod 12118235562053928241991456401) ^ 327519880055511574107877200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (113 : ZMod 12118235562053928241991456401) ^ 295566721025705566877840400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (113 : ZMod 12118235562053928241991456401) ^ 281819431675672749813754800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (113 : ZMod 12118235562053928241991456401) ^ 257834799192636771106201200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (113 : ZMod 12118235562053928241991456401) ^ 228645954001017513999838800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (113 : ZMod 12118235562053928241991456401) ^ 205393823085659800711719600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (113 : ZMod 12118235562053928241991456401) ^ 198659599377933249868712400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_16157647416071904322655275201 : Nat.Prime 16157647416071904322655275201 := by
  apply lucas_primality 16157647416071904322655275201 (71 : ZMod 16157647416071904322655275201)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 16157647416071904322655275201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_11
      · exact prime_fortyOneAM_13
      · exact prime_fortyOneAM_17
      · exact prime_fortyOneAM_19
      · exact prime_fortyOneAM_23
      · exact prime_fortyOneAM_29
      · exact prime_fortyOneAM_31
      · exact prime_fortyOneAM_37
      · exact prime_fortyOneAM_41
      · exact prime_fortyOneAM_43
      · exact prime_fortyOneAM_47
      · exact prime_fortyOneAM_53
      · exact prime_fortyOneAM_59
      · exact prime_fortyOneAM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 16157647416071904322655275201) ^ 8078823708035952161327637600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (71 : ZMod 16157647416071904322655275201) ^ 5385882472023968107551758400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (71 : ZMod 16157647416071904322655275201) ^ 3231529483214380864531055040 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (71 : ZMod 16157647416071904322655275201) ^ 2308235345153129188950753600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (71 : ZMod 16157647416071904322655275201) ^ 1468877037824718574786843200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (71 : ZMod 16157647416071904322655275201) ^ 1242895955082454178665790400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (71 : ZMod 16157647416071904322655275201) ^ 950449848004229666038545600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (71 : ZMod 16157647416071904322655275201) ^ 850402495582731806455540800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (71 : ZMod 16157647416071904322655275201) ^ 702506409394430622724142400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (71 : ZMod 16157647416071904322655275201) ^ 557160255726617390436388800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (71 : ZMod 16157647416071904322655275201) ^ 521214432776513042666299200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (71 : ZMod 16157647416071904322655275201) ^ 436693173407348765477169600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (71 : ZMod 16157647416071904322655275201) ^ 394088961367607422503787200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (71 : ZMod 16157647416071904322655275201) ^ 375759242234230333085006400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (71 : ZMod 16157647416071904322655275201) ^ 343779732256849028141601600 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (71 : ZMod 16157647416071904322655275201) ^ 304861272001356685333118400 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (71 : ZMod 16157647416071904322655275201) ^ 273858430780879734282292800 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (71 : ZMod 16157647416071904322655275201) ^ 264879465837244333158283200 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_48472942248215712967965825671 : Nat.Prime 48472942248215712967965825671 := by
  apply lucas_primality 48472942248215712967965825671 (11 : ZMod 48472942248215712967965825671)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (692470603545938756685226081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (692470603545938756685226081, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_5
      · exact prime_fortyOneAM_7
      · exact prime_fortyOneAM_692470603545938756685226081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 48472942248215712967965825671) ^ 24236471124107856483982912835 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 48472942248215712967965825671) ^ 9694588449643142593593165134 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 48472942248215712967965825671) ^ 6924706035459387566852260810 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (11 : ZMod 48472942248215712967965825671) ^ 70 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem prime_fortyOneAM_48472942248215712967965825673 : Nat.Prime 48472942248215712967965825673 := by
  apply lucas_primality 48472942248215712967965825673 (10 : ZMod 48472942248215712967965825673)
  · rw [← fortyOneAMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1301, 1), (51803, 1), (6707161, 1), (1489347175447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1301, 1), (51803, 1), (6707161, 1), (1489347175447, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyOneAM_2
      · exact prime_fortyOneAM_3
      · exact prime_fortyOneAM_1301
      · exact prime_fortyOneAM_51803
      · exact prime_fortyOneAM_6707161
      · exact prime_fortyOneAM_1489347175447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 48472942248215712967965825673) ^ 24236471124107856483982912836 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 48472942248215712967965825673) ^ 16157647416071904322655275224 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 48472942248215712967965825673) ^ 37258218484408695594132072 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 48472942248215712967965825673) ^ 935716893774795146380824 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 48472942248215712967965825673) ^ 7227043192822673105352 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide
    · change (10 : ZMod 48472942248215712967965825673) ^ 32546435812501176 ≠ 1
      rw [← fortyOneAMFastPow_eq_pow]
      decide

private theorem phi_fortyOneAM_48472942248215712967965825600 : Nat.totient 48472942248215712967965825600 = 6378426106833786214809600000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825600 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_3, prime_fortyOneAM_5, prime_fortyOneAM_7, prime_fortyOneAM_11, prime_fortyOneAM_13, prime_fortyOneAM_17, prime_fortyOneAM_19, prime_fortyOneAM_23, prime_fortyOneAM_29, prime_fortyOneAM_31, prime_fortyOneAM_37, prime_fortyOneAM_41, prime_fortyOneAM_43, prime_fortyOneAM_47, prime_fortyOneAM_53, prime_fortyOneAM_59, prime_fortyOneAM_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825601 : Nat.totient 48472942248215712967965825601 = 48463942627011448097436066048 := by
  rw [← show ((([(6709, 1), (32653, 1), (166949, 1), (1325362503021437, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825601 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_6709, prime_fortyOneAM_32653, prime_fortyOneAM_166949, prime_fortyOneAM_1325362503021437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825602 : Nat.totient 48472942248215712967965825602 = 24236130901033834446888578992 := by
  rw [← show ((([(2, 1), (71237, 1), (340223074022037094262573, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825602 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_71237, prime_fortyOneAM_340223074022037094262573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825603 : Nat.totient 48472942248215712967965825603 = 32315294832143808645310550400 := by
  rw [← show ((([(3, 1), (16157647416071904322655275201, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825603 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_3, prime_fortyOneAM_16157647416071904322655275201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825604 : Nat.totient 48472942248215712967965825604 = 24236471124107856483982912800 := by
  rw [← show ((([(2, 2), (12118235562053928241991456401, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825604 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_12118235562053928241991456401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825605 : Nat.totient 48472942248215712967965825605 = 38029617883168341897441623040 := by
  rw [← show ((([(5, 1), (71, 1), (229, 1), (1069, 1), (41757923, 1), (13357308358237, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825605 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_5, prime_fortyOneAM_71, prime_fortyOneAM_229, prime_fortyOneAM_1069, prime_fortyOneAM_41757923, prime_fortyOneAM_13357308358237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825606 : Nat.totient 48472942248215712967965825606 = 15997569457260813213355000800 := by
  rw [← show ((([(2, 1), (3, 1), (101, 1), (157999, 1), (506258606351371954499, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825606 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_3, prime_fortyOneAM_101, prime_fortyOneAM_157999, prime_fortyOneAM_506258606351371954499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825607 : Nat.totient 48472942248215712967965825607 = 41536244984955319256426382528 := by
  rw [← show ((([(7, 1), (3547, 1), (149627, 1), (13047586499150352329, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825607 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_7, prime_fortyOneAM_3547, prime_fortyOneAM_149627, prime_fortyOneAM_13047586499150352329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825608 : Nat.totient 48472942248215712967965825608 = 24231794545855895021647303680 := by
  rw [← show ((([(2, 3), (5813, 1), (63727, 1), (241781, 1), (917227, 1), (73754173, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825608 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_5813, prime_fortyOneAM_63727, prime_fortyOneAM_241781, prime_fortyOneAM_917227, prime_fortyOneAM_73754173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825609 : Nat.totient 48472942248215712967965825609 = 32315269529245298125397760000 := by
  rw [← show ((([(3, 2), (1307101, 1), (55713781, 1), (73957988809921, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825609 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_3, prime_fortyOneAM_1307101, prime_fortyOneAM_55713781, prime_fortyOneAM_73957988809921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825610 : Nat.totient 48472942248215712967965825610 = 19103152991593435957695283200 := by
  rw [← show ((([(2, 1), (5, 1), (73, 1), (941, 1), (198929, 1), (194388361, 1), (1824813733, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825610 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_5, prime_fortyOneAM_73, prime_fortyOneAM_941, prime_fortyOneAM_198929, prime_fortyOneAM_194388361, prime_fortyOneAM_1824813733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825611 : Nat.totient 48472942248215712967965825611 = 43802441008160947491352282080 := by
  rw [← show ((([(11, 1), (167, 1), (1994649602389, 1), (13228896255227, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825611 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_11, prime_fortyOneAM_167, prime_fortyOneAM_1994649602389, prime_fortyOneAM_13228896255227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825612 : Nat.totient 48472942248215712967965825612 = 16153137806324768512114230720 := by
  rw [← show ((([(2, 2), (3, 1), (3583, 1), (203570467, 1), (5538045946039141, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825612 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_3, prime_fortyOneAM_3583, prime_fortyOneAM_203570467, prime_fortyOneAM_5538045946039141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825613 : Nat.totient 48472942248215712967965825613 = 44743274323843775057805772800 := by
  rw [← show ((([(13, 1), (54851, 1), (272299, 1), (249646472141438849, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825613 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_13, prime_fortyOneAM_54851, prime_fortyOneAM_272299, prime_fortyOneAM_249646472141438849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825614 : Nat.totient 48472942248215712967965825614 = 20773863647361636685601621760 := by
  rw [← show ((([(2, 1), (7, 1), (81853, 1), (31421581, 1), (1346197288565257, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825614 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_7, prime_fortyOneAM_81853, prime_fortyOneAM_31421581, prime_fortyOneAM_1346197288565257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825615 : Nat.totient 48472942248215712967965825615 = 25814225212023983077867392000 := by
  rw [← show ((([(3, 1), (5, 1), (683, 1), (262111, 1), (422057, 1), (42769193807701, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825615 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_3, prime_fortyOneAM_5, prime_fortyOneAM_683, prime_fortyOneAM_262111, prime_fortyOneAM_422057, prime_fortyOneAM_42769193807701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825616 : Nat.totient 48472942248215712967965825616 = 24236471124106959760171220736 := by
  rw [← show ((([(2, 4), (45485416365373, 1), (66605060096137, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825616 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_45485416365373, prime_fortyOneAM_66605060096137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825617 : Nat.totient 48472942248215712967965825617 = 44131025557865439133823139840 := by
  rw [← show ((([(17, 1), (67, 1), (97, 1), (149, 1), (991, 1), (13619, 1), (2983363, 1), (73129513, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825617 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_17, prime_fortyOneAM_67, prime_fortyOneAM_97, prime_fortyOneAM_149, prime_fortyOneAM_991, prime_fortyOneAM_13619, prime_fortyOneAM_2983363, prime_fortyOneAM_73129513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825618 : Nat.totient 48472942248215712967965825618 = 16151349523693005305089721280 := by
  rw [← show ((([(2, 1), (3, 2), (2671, 1), (64969, 1), (15518395153927508599, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825618 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_3, prime_fortyOneAM_2671, prime_fortyOneAM_64969, prime_fortyOneAM_15518395153927508599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825619 : Nat.totient 48472942248215712967965825619 = 45921694416957706998415685184 := by
  rw [← show ((([(19, 1), (1394857, 1), (6186967, 1), (295623051014479, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825619 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_19, prime_fortyOneAM_1394857, prime_fortyOneAM_6186967, prime_fortyOneAM_295623051014479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825620 : Nat.totient 48472942248215712967965825620 = 19389113298566691948010659840 := by
  rw [← show ((([(2, 2), (5, 1), (304897, 1), (2374229903, 1), (3348061788191, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825620 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_5, prime_fortyOneAM_304897, prime_fortyOneAM_2374229903, prime_fortyOneAM_3348061788191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825621 : Nat.totient 48472942248215712967965825621 = 27698823426261737181691372800 := by
  rw [← show ((([(3, 1), (7, 1), (38708441, 1), (59631317757104430761, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825621 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_3, prime_fortyOneAM_7, prime_fortyOneAM_38708441, prime_fortyOneAM_59631317757104430761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825622 : Nat.totient 48472942248215712967965825622 = 22033064265046511011520359680 := by
  rw [← show ((([(2, 1), (11, 2), (241337, 1), (3667245859, 1), (226318511977, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825622 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_11, prime_fortyOneAM_241337, prime_fortyOneAM_3667245859, prime_fortyOneAM_226318511977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825623 : Nat.totient 48472942248215712967965825623 = 46365362008642126733957616184 := by
  rw [← show ((([(23, 1), (759947, 1), (2773245013380264502883, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825623 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_23, prime_fortyOneAM_759947, prime_fortyOneAM_2773245013380264502883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825624 : Nat.totient 48472942248215712967965825624 = 16157647416071904322655275200 := by
  rw [← show ((([(2, 3), (3, 1), (2019705927008988040331909401, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825624 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_3, prime_fortyOneAM_2019705927008988040331909401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825625 : Nat.totient 48472942248215712967965825625 = 38776611072412162452526920000 := by
  rw [← show ((([(5, 4), (22621, 1), (1362367, 1), (2516595694244803, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825625 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_5, prime_fortyOneAM_22621, prime_fortyOneAM_1362367, prime_fortyOneAM_2516595694244803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825626 : Nat.totient 48472942248215712967965825626 = 22065378165796822841294069760 := by
  rw [← show ((([(2, 1), (13, 1), (79, 1), (1249, 1), (3767, 1), (1679261, 1), (2986913749213, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825626 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_13, prime_fortyOneAM_79, prime_fortyOneAM_1249, prime_fortyOneAM_3767, prime_fortyOneAM_1679261, prime_fortyOneAM_2986913749213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825627 : Nat.totient 48472942248215712967965825627 = 32131028278738006875688515840 := by
  rw [← show ((([(3, 4), (241, 1), (839, 1), (2719, 1), (1088494281542954707, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825627 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_3, prime_fortyOneAM_241, prime_fortyOneAM_839, prime_fortyOneAM_2719, prime_fortyOneAM_1088494281542954707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825628 : Nat.totient 48472942248215712967965825628 = 20774118106378162700556782400 := by
  rw [← show ((([(2, 2), (7, 1), (1731176508864846891713065201, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825628 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_7, prime_fortyOneAM_1731176508864846891713065201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825629 : Nat.totient 48472942248215712967965825629 = 46764486258039148996992067200 := by
  rw [← show ((([(29, 1), (1999, 1), (3449, 1), (242435042859187229351, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825629 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_29, prime_fortyOneAM_1999, prime_fortyOneAM_3449, prime_fortyOneAM_242435042859187229351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825630 : Nat.totient 48472942248215712967965825630 = 12888866872532285638360170656 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (347, 1), (4656382540654727470505843, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825630 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_3, prime_fortyOneAM_5, prime_fortyOneAM_347, prime_fortyOneAM_4656382540654727470505843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825631 : Nat.totient 48472942248215712967965825631 = 46819261907755874082116688000 := by
  rw [← show ((([(31, 1), (521, 1), (3001234737676658595007481, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825631 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_31, prime_fortyOneAM_521, prime_fortyOneAM_3001234737676658595007481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825632 : Nat.totient 48472942248215712967965825632 = 24207164629362581271515927040 := by
  rw [← show ((([(2, 5), (827, 1), (1097740871221, 1), (1668568573253, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825632 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_827, prime_fortyOneAM_1097740871221, prime_fortyOneAM_1668568573253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825633 : Nat.totient 48472942248215712967965825633 = 29002778462174160880846402560 := by
  rw [← show ((([(3, 1), (11, 1), (109, 1), (277, 1), (180749, 1), (269155507944894293, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825633 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_3, prime_fortyOneAM_11, prime_fortyOneAM_109, prime_fortyOneAM_277, prime_fortyOneAM_180749, prime_fortyOneAM_269155507944894293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825634 : Nat.totient 48472942248215712967965825634 = 22810796352101511984925094400 := by
  rw [← show ((([(2, 1), (17, 1), (1425674772006344499057818401, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825634 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_17, prime_fortyOneAM_1425674772006344499057818401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825635 : Nat.totient 48472942248215712967965825635 = 33238588970198883926802823776 := by
  rw [← show ((([(5, 1), (7, 1), (5499056474839, 1), (251850697192999, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825635 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_5, prime_fortyOneAM_7, prime_fortyOneAM_5499056474839, prime_fortyOneAM_251850697192999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825636 : Nat.totient 48472942248215712967965825636 = 16157647416071904322655275200 := by
  rw [← show ((([(2, 2), (3, 2), (1346470618005992026887939601, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825636 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_3, prime_fortyOneAM_1346470618005992026887939601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825637 : Nat.totient 48472942248215712967965825637 = 46938472068024279968917340160 := by
  rw [← show ((([(37, 1), (233, 1), (2137, 1), (2631099150712756233281, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825637 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_37, prime_fortyOneAM_233, prime_fortyOneAM_2137, prime_fortyOneAM_2631099150712756233281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825638 : Nat.totient 48472942248215712967965825638 = 22876140932017263876497490720 := by
  rw [← show ((([(2, 1), (19, 1), (271, 1), (28001123627, 1), (168101285719853, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825638 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_19, prime_fortyOneAM_271, prime_fortyOneAM_28001123627, prime_fortyOneAM_168101285719853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825639 : Nat.totient 48472942248215712967965825639 = 29829231327411592525138082400 := by
  rw [← show ((([(3, 1), (13, 1), (109831, 1), (11316440304490118260471, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825639 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_3, prime_fortyOneAM_13, prime_fortyOneAM_109831, prime_fortyOneAM_11316440304490118260471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825640 : Nat.totient 48472942248215712967965825640 = 19389176890415615625351572800 := by
  rw [← show ((([(2, 3), (5, 1), (2185762511, 1), (554416845428909831, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825640 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_5, prime_fortyOneAM_2185762511, prime_fortyOneAM_554416845428909831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825641 : Nat.totient 48472942248215712967965825641 = 46822193114131825580039047680 := by
  rw [← show ((([(41, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825641 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_41, prime_fortyOneAM_103, prime_fortyOneAM_5009, prime_fortyOneAM_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825642 : Nat.totient 48472942248215712967965825642 = 13693800310990553303766057600 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (89, 1), (35261959, 1), (367750818909779951, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825642 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_3, prime_fortyOneAM_7, prime_fortyOneAM_89, prime_fortyOneAM_35261959, prime_fortyOneAM_367750818909779951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825643 : Nat.totient 48472942248215712967965825643 = 47345664521513021968710806400 := by
  rw [← show ((([(43, 1), (1127277726702690999255019201, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825643 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_43, prime_fortyOneAM_1127277726702690999255019201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825644 : Nat.totient 48472942248215712967965825644 = 22033155566284950871201029840 := by
  rw [← show ((([(2, 2), (11, 1), (20291582887, 1), (54291367238498023, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825644 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_11, prime_fortyOneAM_20291582887, prime_fortyOneAM_54291367238498023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825645 : Nat.totient 48472942248215712967965825645 = 25839740826630602717642180736 := by
  rw [← show ((([(3, 2), (5, 1), (2069, 1), (520626628518508275258749, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825645 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_3, prime_fortyOneAM_5, prime_fortyOneAM_2069, prime_fortyOneAM_520626628518508275258749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825646 : Nat.totient 48472942248215712967965825646 = 23182426019190625088636709304 := by
  rw [← show ((([(2, 1), (23, 1), (81203, 1), (12976855708430057191067, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825646 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_23, prime_fortyOneAM_81203, prime_fortyOneAM_12976855708430057191067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825647 : Nat.totient 48472942248215712967965825647 = 47387892743889399338705118720 := by
  rw [← show ((([(47, 1), (1109, 1), (4391, 1), (358349, 1), (12445397, 1), (47488843, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825647 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_47, prime_fortyOneAM_1109, prime_fortyOneAM_4391, prime_fortyOneAM_358349, prime_fortyOneAM_12445397, prime_fortyOneAM_47488843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825648 : Nat.totient 48472942248215712967965825648 = 16137932816695059120363191040 := by
  rw [← show ((([(2, 4), (3, 1), (877, 1), (12503, 1), (92096753199254438471, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825648 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_3, prime_fortyOneAM_877, prime_fortyOneAM_12503, prime_fortyOneAM_92096753199254438471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825649 : Nat.totient 48472942248215712967965825649 = 41045375110811809219290385920 := by
  rw [← show ((([(7, 2), (83, 1), (25841, 1), (60887, 1), (2369183, 1), (3197368627, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825649 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_7, prime_fortyOneAM_83, prime_fortyOneAM_25841, prime_fortyOneAM_60887, prime_fortyOneAM_2369183, prime_fortyOneAM_3197368627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825650 : Nat.totient 48472942248215712967965825650 = 19297173021900327408821299200 := by
  rw [← show ((([(2, 1), (5, 2), (211, 1), (174157, 1), (15565127, 1), (1694936056097, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825650 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_5, prime_fortyOneAM_211, prime_fortyOneAM_174157, prime_fortyOneAM_15565127, prime_fortyOneAM_1694936056097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825651 : Nat.totient 48472942248215712967965825651 = 30414363358179923825606236800 := by
  rw [← show ((([(3, 1), (17, 1), (957091, 1), (993061107046487393611, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825651 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_3, prime_fortyOneAM_17, prime_fortyOneAM_957091, prime_fortyOneAM_993061107046487393611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825652 : Nat.totient 48472942248215712967965825652 = 22321625775702043894954779552 := by
  rw [← show ((([(2, 2), (13, 2), (443, 1), (161863512122215772529839, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825652 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_13, prime_fortyOneAM_443, prime_fortyOneAM_161863512122215772529839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825653 : Nat.totient 48472942248215712967965825653 = 47557636529410596007955128320 := by
  rw [← show ((([(53, 1), (65881, 1), (2374552097, 1), (5846307133193, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825653 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_53, prime_fortyOneAM_65881, prime_fortyOneAM_2374552097, prime_fortyOneAM_5846307133193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825654 : Nat.totient 48472942248215712967965825654 = 16157482758861333829686876672 := by
  rw [← show ((([(2, 1), (3, 3), (98129, 1), (9147622809471831479569, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825654 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_3, prime_fortyOneAM_98129, prime_fortyOneAM_9147622809471831479569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825655 : Nat.totient 48472942248215712967965825655 = 35191309758761238884716320000 := by
  rw [← show ((([(5, 1), (11, 1), (571, 1), (3872145691, 1), (398610646850761, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825655 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_5, prime_fortyOneAM_11, prime_fortyOneAM_571, prime_fortyOneAM_3872145691, prime_fortyOneAM_398610646850761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825656 : Nat.totient 48472942248215712967965825656 = 20773993611312593246060873568 := by
  rw [← show ((([(2, 3), (7, 1), (166867, 1), (5187294398727270496003, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825656 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_7, prime_fortyOneAM_166867, prime_fortyOneAM_5187294398727270496003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825657 : Nat.totient 48472942248215712967965825657 = 30614099454287723330613688320 := by
  rw [← show ((([(3, 1), (19, 1), (88261, 1), (703393, 1), (13698015089224237, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825657 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_3, prime_fortyOneAM_19, prime_fortyOneAM_88261, prime_fortyOneAM_703393, prime_fortyOneAM_13698015089224237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825658 : Nat.totient 48472942248215712967965825658 = 23400730740485370432175509312 := by
  rw [← show ((([(2, 1), (29, 1), (719141144749, 1), (1162136792884549, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825658 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_29, prime_fortyOneAM_719141144749, prime_fortyOneAM_1162136792884549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825659 : Nat.totient 48472942248215712967965825659 = 47339165842886495870530156800 := by
  rw [← show ((([(59, 1), (173, 1), (1289, 1), (8348551, 1), (441303371073883, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825659 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_59, prime_fortyOneAM_173, prime_fortyOneAM_1289, prime_fortyOneAM_8348551, prime_fortyOneAM_441303371073883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825660 : Nat.totient 48472942248215712967965825660 = 12926117932857523458124220160 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (807882370803595216132763761, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825660 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_3, prime_fortyOneAM_5, prime_fortyOneAM_807882370803595216132763761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825661 : Nat.totient 48472942248215712967965825661 = 47123028575407991244553228800 := by
  rw [← show ((([(61, 1), (139, 1), (223, 1), (159796002313, 1), (160429405141, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825661 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_61, prime_fortyOneAM_139, prime_fortyOneAM_223, prime_fortyOneAM_159796002313, prime_fortyOneAM_160429405141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825662 : Nat.totient 48472942248215712967965825662 = 23454649168498210198716073560 := by
  rw [← show ((([(2, 1), (31, 1), (76537907, 1), (10214829223965708443, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825662 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_31, prime_fortyOneAM_76537907, prime_fortyOneAM_10214829223965708443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825663 : Nat.totient 48472942248215712967965825663 = 27698801656707880376434163712 := by
  rw [← show ((([(3, 2), (7, 1), (1231873, 1), (624586935274748070337, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825663 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_3, prime_fortyOneAM_7, prime_fortyOneAM_1231873, prime_fortyOneAM_624586935274748070337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825664 : Nat.totient 48472942248215712967965825664 = 24082083487911044328953785344 := by
  rw [← show ((([(2, 7), (157, 1), (1583447, 1), (1523302756799014447, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825664 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_157, prime_fortyOneAM_1583447, prime_fortyOneAM_1523302756799014447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825665 : Nat.totient 48472942248215712967965825665 = 35753628484273600588345217280 := by
  rw [← show ((([(5, 1), (13, 1), (1091, 1), (3989, 1), (171355180240039693759, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825665 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_5, prime_fortyOneAM_13, prime_fortyOneAM_1091, prime_fortyOneAM_3989, prime_fortyOneAM_171355180240039693759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825666 : Nat.totient 48472942248215712967965825666 = 14688130985465300613764987840 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (22973, 1), (31969639094256705149237, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825666 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_3, prime_fortyOneAM_11, prime_fortyOneAM_22973, prime_fortyOneAM_31969639094256705149237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825667 : Nat.totient 48472942248215712967965825667 = 48175561763405839534101890112 := by
  rw [← show ((([(163, 1), (118880539, 1), (1063799003, 1), (2351480777, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825667 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_163, prime_fortyOneAM_118880539, prime_fortyOneAM_1063799003, prime_fortyOneAM_2351480777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825668 : Nat.totient 48472942248215712967965825668 = 22796386499699679065161983104 := by
  rw [← show ((([(2, 2), (17, 1), (1583, 1), (450307887557278742595647, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825668 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_17, prime_fortyOneAM_1583, prime_fortyOneAM_450307887557278742595647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825669 : Nat.totient 48472942248215712967965825669 = 30910282013354947399862264632 := by
  rw [← show ((([(3, 1), (23, 2), (30543756930192635770614887, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825669 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_3, prime_fortyOneAM_23, prime_fortyOneAM_30543756930192635770614887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825670 : Nat.totient 48472942248215712967965825670 = 16619294485102530160445425920 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (692470603545938756685226081, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825670 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_5, prime_fortyOneAM_7, prime_fortyOneAM_692470603545938756685226081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825671 : Nat.totient 48472942248215712967965825671 = 48472942248215712967965825670 := by
  rw [← show ((([(48472942248215712967965825671, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825671 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_48472942248215712967965825671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825672 : Nat.totient 48472942248215712967965825672 = 16144913936895060870843264000 := by
  rw [← show ((([(2, 3), (3, 2), (1301, 1), (51803, 1), (6707161, 1), (1489347175447, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825672 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_3, prime_fortyOneAM_1301, prime_fortyOneAM_51803, prime_fortyOneAM_6707161, prime_fortyOneAM_1489347175447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825673 : Nat.totient 48472942248215712967965825673 = 48472942248215712967965825672 := by
  rw [← show ((([(48472942248215712967965825673, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825673 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_48472942248215712967965825673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825674 : Nat.totient 48472942248215712967965825674 = 23545318910857603813233709632 := by
  rw [← show ((([(2, 1), (37, 1), (653, 1), (28712733319, 1), (34936544158643, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825674 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_37, prime_fortyOneAM_653, prime_fortyOneAM_28712733319, prime_fortyOneAM_34936544158643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825675 : Nat.totient 48472942248215712967965825675 = 25852231098725820538837082400 := by
  rw [← show ((([(3, 1), (5, 2), (5423179, 1), (119174730659429860771, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825675 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_3, prime_fortyOneAM_5, prime_fortyOneAM_5423179, prime_fortyOneAM_119174730659429860771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825676 : Nat.totient 48472942248215712967965825676 = 22601599327924795472122080000 := by
  rw [← show ((([(2, 2), (19, 1), (71, 1), (631, 1), (14236331146337109770801, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825676 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_19, prime_fortyOneAM_71, prime_fortyOneAM_631, prime_fortyOneAM_14236331146337109770801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825677 : Nat.totient 48472942248215712967965825677 = 37750673817588516501580044480 := by
  rw [← show ((([(7, 1), (11, 1), (1847, 1), (1432182397, 1), (237981627128339, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825677 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_7, prime_fortyOneAM_11, prime_fortyOneAM_1847, prime_fortyOneAM_1432182397, prime_fortyOneAM_237981627128339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825678 : Nat.totient 48472942248215712967965825678 = 14775355719525447271097763840 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (107, 1), (2781817, 1), (64512521, 1), (32362974499, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825678 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_3, prime_fortyOneAM_13, prime_fortyOneAM_107, prime_fortyOneAM_2781817, prime_fortyOneAM_64512521, prime_fortyOneAM_32362974499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825679 : Nat.totient 48472942248215712967965825679 = 48368249068413951168898944384 := by
  rw [← show ((([(463, 1), (104693179801761799066880833, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825679 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_463, prime_fortyOneAM_104693179801761799066880833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825680 : Nat.totient 48472942248215712967965825680 = 19217233192141797924333551616 := by
  rw [← show ((([(2, 4), (5, 1), (113, 1), (92737, 1), (127399, 1), (453849529498259, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825680 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_5, prime_fortyOneAM_113, prime_fortyOneAM_92737, prime_fortyOneAM_127399, prime_fortyOneAM_453849529498259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825681 : Nat.totient 48472942248215712967965825681 = 32315293684657167851340859392 := by
  rw [← show ((([(3, 3), (31004833, 1), (307622353, 1), (188229778547, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825681 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_3, prime_fortyOneAM_31004833, prime_fortyOneAM_307622353, prime_fortyOneAM_188229778547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825682 : Nat.totient 48472942248215712967965825682 = 23645337662716489815288244000 := by
  rw [← show ((([(2, 1), (41, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825682 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_41, prime_fortyOneAM_1222615931, prime_fortyOneAM_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825683 : Nat.totient 48472942248215712967965825683 = 47808872218176571481290732800 := by
  rw [← show ((([(73, 1), (1243741, 1), (6105223, 1), (6600031, 1), (13249487, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825683 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_73, prime_fortyOneAM_1243741, prime_fortyOneAM_6105223, prime_fortyOneAM_6600031, prime_fortyOneAM_13249487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825684 : Nat.totient 48472942248215712967965825684 = 13642704428069241176485049568 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (67, 1), (8612818452063914884144603, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825684 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_3, prime_fortyOneAM_7, prime_fortyOneAM_67, prime_fortyOneAM_8612818452063914884144603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825685 : Nat.totient 48472942248215712967965825685 = 36497181369553763969789263872 := by
  rw [← show ((([(5, 1), (17, 2), (394453, 1), (136460353, 1), (623203352237, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825685 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_5, prime_fortyOneAM_17, prime_fortyOneAM_394453, prime_fortyOneAM_136460353, prime_fortyOneAM_623203352237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825686 : Nat.totient 48472942248215712967965825686 = 23486412847947216539893748640 := by
  rw [← show ((([(2, 1), (43, 1), (127, 1), (1225883, 1), (3620330232355834061, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825686 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_43, prime_fortyOneAM_127, prime_fortyOneAM_1225883, prime_fortyOneAM_3620330232355834061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825687 : Nat.totient 48472942248215712967965825687 = 31200941896285549752896007168 := by
  rw [← show ((([(3, 1), (29, 1), (1308499, 1), (3636667, 1), (117085522488097, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825687 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_3, prime_fortyOneAM_29, prime_fortyOneAM_1308499, prime_fortyOneAM_3636667, prime_fortyOneAM_117085522488097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825688 : Nat.totient 48472942248215712967965825688 = 22033155567370778621802648000 := by
  rw [← show ((([(2, 3), (11, 1), (550828889184269465545066201, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825688 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_11, prime_fortyOneAM_550828889184269465545066201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825689 : Nat.totient 48472942248215712967965825689 = 48089005145613072982238676480 := by
  rw [← show ((([(131, 1), (3457, 1), (107035713019972117570867, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825689 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_131, prime_fortyOneAM_3457, prime_fortyOneAM_107035713019972117570867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825690 : Nat.totient 48472942248215712967965825690 = 12911070065648143337684008416 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (859, 1), (626994467057505018341299, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825690 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_3, prime_fortyOneAM_5, prime_fortyOneAM_859, prime_fortyOneAM_626994467057505018341299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825691 : Nat.totient 48472942248215712967965825691 = 38351909081848574460939801984 := by
  rw [← show ((([(7, 1), (13, 1), (124133, 1), (4291120773970962637997, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825691 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_7, prime_fortyOneAM_13, prime_fortyOneAM_124133, prime_fortyOneAM_4291120773970962637997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825692 : Nat.totient 48472942248215712967965825692 = 23044577836558670772181401600 := by
  rw [← show ((([(2, 2), (23, 1), (179, 1), (2689, 1), (478411, 1), (2288055551167361, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825692 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_23, prime_fortyOneAM_179, prime_fortyOneAM_2689, prime_fortyOneAM_478411, prime_fortyOneAM_2288055551167361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825693 : Nat.totient 48472942248215712967965825693 = 31250670887732366111412602880 := by
  rw [← show ((([(3, 1), (31, 1), (1409, 1), (583458069907, 1), (634009534427, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825693 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_3, prime_fortyOneAM_31, prime_fortyOneAM_1409, prime_fortyOneAM_583458069907, prime_fortyOneAM_634009534427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825694 : Nat.totient 48472942248215712967965825694 = 23720801525718771147236560512 := by
  rw [← show ((([(2, 1), (47, 1), (6777296554297, 1), (76087802009833, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825694 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_47, prime_fortyOneAM_6777296554297, prime_fortyOneAM_76087802009833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825695 : Nat.totient 48472942248215712967965825695 = 36725119942031623470867333120 := by
  rw [← show ((([(5, 1), (19, 2), (3673, 1), (22777, 1), (56209, 1), (5710825188091, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825695 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_5, prime_fortyOneAM_19, prime_fortyOneAM_3673, prime_fortyOneAM_22777, prime_fortyOneAM_56209, prime_fortyOneAM_5710825188091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825696 : Nat.totient 48472942248215712967965825696 = 16132095517358691853361971200 := by
  rw [← show ((([(2, 5), (3, 1), (673, 1), (10799, 1), (325813, 1), (213236298175301, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825696 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_3, prime_fortyOneAM_673, prime_fortyOneAM_10799, prime_fortyOneAM_325813, prime_fortyOneAM_213236298175301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825697 : Nat.totient 48472942248215712967965825697 = 48472937585576941228768165392 := by
  rw [← show ((([(10400987, 1), (24673093343, 1), (188886633517, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825697 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_10400987, prime_fortyOneAM_24673093343, prime_fortyOneAM_188886633517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825698 : Nat.totient 48472942248215712967965825698 = 20774118106378162700556782400 := by
  rw [← show ((([(2, 1), (7, 2), (494621859675670540489447201, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825698 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_7, prime_fortyOneAM_494621859675670540489447201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825699 : Nat.totient 48472942248215712967965825699 = 29268330566347519824433536000 := by
  rw [← show ((([(3, 2), (11, 1), (269, 1), (20037513329, 1), (90838108578901, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825699 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_3, prime_fortyOneAM_11, prime_fortyOneAM_269, prime_fortyOneAM_20037513329, prime_fortyOneAM_90838108578901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyOneAM_48472942248215712967965825700 : Nat.totient 48472942248215712967965825700 = 19387378441174858947951395200 := by
  rw [← show ((([(2, 2), (5, 2), (10781, 1), (44961452785655980862597, 1)] : List FactorBlock).map factorBlockValue).prod) = 48472942248215712967965825700 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyOneAM_2, prime_fortyOneAM_5, prime_fortyOneAM_10781, prime_fortyOneAM_44961452785655980862597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FortyOneAM : certifiedKill 1 48472942248215712967965825599 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fortyOneAM_48472942248215712967965825600, phi_fortyOneAM_48472942248215712967965825601, phi_fortyOneAM_48472942248215712967965825602,
    phi_fortyOneAM_48472942248215712967965825603, phi_fortyOneAM_48472942248215712967965825604, phi_fortyOneAM_48472942248215712967965825605,
    phi_fortyOneAM_48472942248215712967965825606, phi_fortyOneAM_48472942248215712967965825607, phi_fortyOneAM_48472942248215712967965825608,
    phi_fortyOneAM_48472942248215712967965825609, phi_fortyOneAM_48472942248215712967965825610, phi_fortyOneAM_48472942248215712967965825611,
    phi_fortyOneAM_48472942248215712967965825612, phi_fortyOneAM_48472942248215712967965825613, phi_fortyOneAM_48472942248215712967965825614,
    phi_fortyOneAM_48472942248215712967965825615, phi_fortyOneAM_48472942248215712967965825616, phi_fortyOneAM_48472942248215712967965825617,
    phi_fortyOneAM_48472942248215712967965825618, phi_fortyOneAM_48472942248215712967965825619, phi_fortyOneAM_48472942248215712967965825620,
    phi_fortyOneAM_48472942248215712967965825621, phi_fortyOneAM_48472942248215712967965825622, phi_fortyOneAM_48472942248215712967965825623,
    phi_fortyOneAM_48472942248215712967965825624, phi_fortyOneAM_48472942248215712967965825625, phi_fortyOneAM_48472942248215712967965825626,
    phi_fortyOneAM_48472942248215712967965825627, phi_fortyOneAM_48472942248215712967965825628, phi_fortyOneAM_48472942248215712967965825629,
    phi_fortyOneAM_48472942248215712967965825630, phi_fortyOneAM_48472942248215712967965825631, phi_fortyOneAM_48472942248215712967965825632,
    phi_fortyOneAM_48472942248215712967965825633, phi_fortyOneAM_48472942248215712967965825634, phi_fortyOneAM_48472942248215712967965825635,
    phi_fortyOneAM_48472942248215712967965825636, phi_fortyOneAM_48472942248215712967965825637, phi_fortyOneAM_48472942248215712967965825638,
    phi_fortyOneAM_48472942248215712967965825639, phi_fortyOneAM_48472942248215712967965825640, phi_fortyOneAM_48472942248215712967965825641,
    phi_fortyOneAM_48472942248215712967965825642, phi_fortyOneAM_48472942248215712967965825643, phi_fortyOneAM_48472942248215712967965825644,
    phi_fortyOneAM_48472942248215712967965825645, phi_fortyOneAM_48472942248215712967965825646, phi_fortyOneAM_48472942248215712967965825647,
    phi_fortyOneAM_48472942248215712967965825648, phi_fortyOneAM_48472942248215712967965825649, phi_fortyOneAM_48472942248215712967965825650,
    phi_fortyOneAM_48472942248215712967965825651, phi_fortyOneAM_48472942248215712967965825652, phi_fortyOneAM_48472942248215712967965825653,
    phi_fortyOneAM_48472942248215712967965825654, phi_fortyOneAM_48472942248215712967965825655, phi_fortyOneAM_48472942248215712967965825656,
    phi_fortyOneAM_48472942248215712967965825657, phi_fortyOneAM_48472942248215712967965825658, phi_fortyOneAM_48472942248215712967965825659,
    phi_fortyOneAM_48472942248215712967965825660, phi_fortyOneAM_48472942248215712967965825661, phi_fortyOneAM_48472942248215712967965825662,
    phi_fortyOneAM_48472942248215712967965825663, phi_fortyOneAM_48472942248215712967965825664, phi_fortyOneAM_48472942248215712967965825665,
    phi_fortyOneAM_48472942248215712967965825666, phi_fortyOneAM_48472942248215712967965825667, phi_fortyOneAM_48472942248215712967965825668,
    phi_fortyOneAM_48472942248215712967965825669, phi_fortyOneAM_48472942248215712967965825670, phi_fortyOneAM_48472942248215712967965825671,
    phi_fortyOneAM_48472942248215712967965825672, phi_fortyOneAM_48472942248215712967965825673, phi_fortyOneAM_48472942248215712967965825674,
    phi_fortyOneAM_48472942248215712967965825675, phi_fortyOneAM_48472942248215712967965825676, phi_fortyOneAM_48472942248215712967965825677,
    phi_fortyOneAM_48472942248215712967965825678, phi_fortyOneAM_48472942248215712967965825679, phi_fortyOneAM_48472942248215712967965825680,
    phi_fortyOneAM_48472942248215712967965825681, phi_fortyOneAM_48472942248215712967965825682, phi_fortyOneAM_48472942248215712967965825683,
    phi_fortyOneAM_48472942248215712967965825684, phi_fortyOneAM_48472942248215712967965825685, phi_fortyOneAM_48472942248215712967965825686,
    phi_fortyOneAM_48472942248215712967965825687, phi_fortyOneAM_48472942248215712967965825688, phi_fortyOneAM_48472942248215712967965825689,
    phi_fortyOneAM_48472942248215712967965825690, phi_fortyOneAM_48472942248215712967965825691, phi_fortyOneAM_48472942248215712967965825692,
    phi_fortyOneAM_48472942248215712967965825693, phi_fortyOneAM_48472942248215712967965825694, phi_fortyOneAM_48472942248215712967965825695,
    phi_fortyOneAM_48472942248215712967965825696, phi_fortyOneAM_48472942248215712967965825697, phi_fortyOneAM_48472942248215712967965825698,
    phi_fortyOneAM_48472942248215712967965825699, phi_fortyOneAM_48472942248215712967965825700]

end TotientTailPeriodKiller
end Erdos249257
