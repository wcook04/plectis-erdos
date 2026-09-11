import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def seventyFourBTFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem seventyFourBTFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : seventyFourBTFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [seventyFourBTFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [seventyFourBTFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then seventyFourBTFastPow a n * seventyFourBTFastPow a n * a else seventyFourBTFastPow a n * seventyFourBTFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_seventyFourBT_2 : Nat.Prime 2 := by norm_num
private theorem prime_seventyFourBT_3 : Nat.Prime 3 := by norm_num
private theorem prime_seventyFourBT_5 : Nat.Prime 5 := by norm_num
private theorem prime_seventyFourBT_7 : Nat.Prime 7 := by norm_num
private theorem prime_seventyFourBT_11 : Nat.Prime 11 := by norm_num
private theorem prime_seventyFourBT_13 : Nat.Prime 13 := by norm_num
private theorem prime_seventyFourBT_17 : Nat.Prime 17 := by norm_num
private theorem prime_seventyFourBT_19 : Nat.Prime 19 := by norm_num
private theorem prime_seventyFourBT_23 : Nat.Prime 23 := by norm_num
private theorem prime_seventyFourBT_29 : Nat.Prime 29 := by norm_num
private theorem prime_seventyFourBT_31 : Nat.Prime 31 := by norm_num
private theorem prime_seventyFourBT_37 : Nat.Prime 37 := by norm_num
private theorem prime_seventyFourBT_41 : Nat.Prime 41 := by norm_num
private theorem prime_seventyFourBT_43 : Nat.Prime 43 := by norm_num
private theorem prime_seventyFourBT_47 : Nat.Prime 47 := by norm_num
private theorem prime_seventyFourBT_53 : Nat.Prime 53 := by norm_num
private theorem prime_seventyFourBT_59 : Nat.Prime 59 := by norm_num
private theorem prime_seventyFourBT_61 : Nat.Prime 61 := by norm_num
private theorem prime_seventyFourBT_67 : Nat.Prime 67 := by norm_num
private theorem prime_seventyFourBT_71 : Nat.Prime 71 := by norm_num
private theorem prime_seventyFourBT_73 : Nat.Prime 73 := by norm_num
private theorem prime_seventyFourBT_79 : Nat.Prime 79 := by norm_num
private theorem prime_seventyFourBT_83 : Nat.Prime 83 := by norm_num
private theorem prime_seventyFourBT_89 : Nat.Prime 89 := by norm_num
private theorem prime_seventyFourBT_97 : Nat.Prime 97 := by norm_num
private theorem prime_seventyFourBT_101 : Nat.Prime 101 := by norm_num
private theorem prime_seventyFourBT_103 : Nat.Prime 103 := by norm_num
private theorem prime_seventyFourBT_107 : Nat.Prime 107 := by norm_num
private theorem prime_seventyFourBT_109 : Nat.Prime 109 := by norm_num
private theorem prime_seventyFourBT_113 : Nat.Prime 113 := by norm_num
private theorem prime_seventyFourBT_127 : Nat.Prime 127 := by norm_num
private theorem prime_seventyFourBT_131 : Nat.Prime 131 := by norm_num
private theorem prime_seventyFourBT_137 : Nat.Prime 137 := by norm_num
private theorem prime_seventyFourBT_149 : Nat.Prime 149 := by norm_num
private theorem prime_seventyFourBT_151 : Nat.Prime 151 := by norm_num
private theorem prime_seventyFourBT_163 : Nat.Prime 163 := by norm_num
private theorem prime_seventyFourBT_167 : Nat.Prime 167 := by norm_num
private theorem prime_seventyFourBT_173 : Nat.Prime 173 := by norm_num
private theorem prime_seventyFourBT_179 : Nat.Prime 179 := by norm_num
private theorem prime_seventyFourBT_181 : Nat.Prime 181 := by norm_num
private theorem prime_seventyFourBT_191 : Nat.Prime 191 := by norm_num
private theorem prime_seventyFourBT_193 : Nat.Prime 193 := by norm_num
private theorem prime_seventyFourBT_197 : Nat.Prime 197 := by norm_num
private theorem prime_seventyFourBT_199 : Nat.Prime 199 := by norm_num
private theorem prime_seventyFourBT_211 : Nat.Prime 211 := by norm_num
private theorem prime_seventyFourBT_223 : Nat.Prime 223 := by norm_num
private theorem prime_seventyFourBT_227 : Nat.Prime 227 := by norm_num
private theorem prime_seventyFourBT_229 : Nat.Prime 229 := by norm_num
private theorem prime_seventyFourBT_233 : Nat.Prime 233 := by norm_num
private theorem prime_seventyFourBT_239 : Nat.Prime 239 := by norm_num
private theorem prime_seventyFourBT_241 : Nat.Prime 241 := by norm_num
private theorem prime_seventyFourBT_251 : Nat.Prime 251 := by norm_num
private theorem prime_seventyFourBT_263 : Nat.Prime 263 := by norm_num
private theorem prime_seventyFourBT_269 : Nat.Prime 269 := by norm_num
private theorem prime_seventyFourBT_277 : Nat.Prime 277 := by norm_num
private theorem prime_seventyFourBT_293 : Nat.Prime 293 := by norm_num
private theorem prime_seventyFourBT_307 : Nat.Prime 307 := by norm_num
private theorem prime_seventyFourBT_311 : Nat.Prime 311 := by norm_num
private theorem prime_seventyFourBT_313 : Nat.Prime 313 := by norm_num
private theorem prime_seventyFourBT_317 : Nat.Prime 317 := by norm_num
private theorem prime_seventyFourBT_331 : Nat.Prime 331 := by norm_num
private theorem prime_seventyFourBT_337 : Nat.Prime 337 := by norm_num
private theorem prime_seventyFourBT_347 : Nat.Prime 347 := by norm_num
private theorem prime_seventyFourBT_353 : Nat.Prime 353 := by norm_num
private theorem prime_seventyFourBT_359 : Nat.Prime 359 := by norm_num
private theorem prime_seventyFourBT_379 : Nat.Prime 379 := by norm_num
private theorem prime_seventyFourBT_383 : Nat.Prime 383 := by norm_num
private theorem prime_seventyFourBT_389 : Nat.Prime 389 := by norm_num
private theorem prime_seventyFourBT_397 : Nat.Prime 397 := by norm_num
private theorem prime_seventyFourBT_421 : Nat.Prime 421 := by norm_num
private theorem prime_seventyFourBT_431 : Nat.Prime 431 := by norm_num
private theorem prime_seventyFourBT_443 : Nat.Prime 443 := by norm_num
private theorem prime_seventyFourBT_449 : Nat.Prime 449 := by norm_num
private theorem prime_seventyFourBT_461 : Nat.Prime 461 := by norm_num
private theorem prime_seventyFourBT_463 : Nat.Prime 463 := by norm_num
private theorem prime_seventyFourBT_479 : Nat.Prime 479 := by norm_num
private theorem prime_seventyFourBT_487 : Nat.Prime 487 := by norm_num
private theorem prime_seventyFourBT_503 : Nat.Prime 503 := by norm_num
private theorem prime_seventyFourBT_521 : Nat.Prime 521 := by norm_num
private theorem prime_seventyFourBT_569 : Nat.Prime 569 := by norm_num
private theorem prime_seventyFourBT_593 : Nat.Prime 593 := by norm_num
private theorem prime_seventyFourBT_641 : Nat.Prime 641 := by norm_num
private theorem prime_seventyFourBT_653 : Nat.Prime 653 := by norm_num
private theorem prime_seventyFourBT_661 : Nat.Prime 661 := by norm_num
private theorem prime_seventyFourBT_673 : Nat.Prime 673 := by norm_num
private theorem prime_seventyFourBT_683 : Nat.Prime 683 := by norm_num
private theorem prime_seventyFourBT_727 : Nat.Prime 727 := by norm_num
private theorem prime_seventyFourBT_743 : Nat.Prime 743 := by norm_num
private theorem prime_seventyFourBT_751 : Nat.Prime 751 := by norm_num
private theorem prime_seventyFourBT_769 : Nat.Prime 769 := by norm_num
private theorem prime_seventyFourBT_773 : Nat.Prime 773 := by norm_num
private theorem prime_seventyFourBT_787 : Nat.Prime 787 := by norm_num
private theorem prime_seventyFourBT_859 : Nat.Prime 859 := by norm_num
private theorem prime_seventyFourBT_883 : Nat.Prime 883 := by norm_num
private theorem prime_seventyFourBT_907 : Nat.Prime 907 := by norm_num
private theorem prime_seventyFourBT_911 : Nat.Prime 911 := by norm_num
private theorem prime_seventyFourBT_919 : Nat.Prime 919 := by norm_num
private theorem prime_seventyFourBT_937 : Nat.Prime 937 := by norm_num
private theorem prime_seventyFourBT_947 : Nat.Prime 947 := by norm_num
private theorem prime_seventyFourBT_971 : Nat.Prime 971 := by norm_num
private theorem prime_seventyFourBT_977 : Nat.Prime 977 := by norm_num
private theorem prime_seventyFourBT_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_seventyFourBT_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_seventyFourBT_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_seventyFourBT_1039 : Nat.Prime 1039 := by norm_num
private theorem prime_seventyFourBT_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_seventyFourBT_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_seventyFourBT_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_seventyFourBT_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_seventyFourBT_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_seventyFourBT_1171 : Nat.Prime 1171 := by norm_num
private theorem prime_seventyFourBT_1181 : Nat.Prime 1181 := by norm_num
private theorem prime_seventyFourBT_1193 : Nat.Prime 1193 := by norm_num
private theorem prime_seventyFourBT_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_seventyFourBT_1283 : Nat.Prime 1283 := by norm_num
private theorem prime_seventyFourBT_1297 : Nat.Prime 1297 := by norm_num
private theorem prime_seventyFourBT_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_seventyFourBT_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_seventyFourBT_1489 : Nat.Prime 1489 := by norm_num
private theorem prime_seventyFourBT_1543 : Nat.Prime 1543 := by norm_num
private theorem prime_seventyFourBT_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_seventyFourBT_1579 : Nat.Prime 1579 := by norm_num
private theorem prime_seventyFourBT_1597 : Nat.Prime 1597 := by norm_num
private theorem prime_seventyFourBT_1741 : Nat.Prime 1741 := by norm_num
private theorem prime_seventyFourBT_1777 : Nat.Prime 1777 := by norm_num
private theorem prime_seventyFourBT_1783 : Nat.Prime 1783 := by norm_num
private theorem prime_seventyFourBT_1931 : Nat.Prime 1931 := by norm_num
private theorem prime_seventyFourBT_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_seventyFourBT_2029 : Nat.Prime 2029 := by norm_num
private theorem prime_seventyFourBT_2087 : Nat.Prime 2087 := by norm_num
private theorem prime_seventyFourBT_2131 : Nat.Prime 2131 := by norm_num
private theorem prime_seventyFourBT_2207 : Nat.Prime 2207 := by norm_num
private theorem prime_seventyFourBT_2221 : Nat.Prime 2221 := by norm_num
private theorem prime_seventyFourBT_2339 : Nat.Prime 2339 := by norm_num
private theorem prime_seventyFourBT_2347 : Nat.Prime 2347 := by norm_num
private theorem prime_seventyFourBT_2351 : Nat.Prime 2351 := by norm_num
private theorem prime_seventyFourBT_2423 : Nat.Prime 2423 := by norm_num
private theorem prime_seventyFourBT_2467 : Nat.Prime 2467 := by norm_num
private theorem prime_seventyFourBT_2477 : Nat.Prime 2477 := by norm_num
private theorem prime_seventyFourBT_2521 : Nat.Prime 2521 := by norm_num
private theorem prime_seventyFourBT_2621 : Nat.Prime 2621 := by norm_num
private theorem prime_seventyFourBT_2633 : Nat.Prime 2633 := by norm_num
private theorem prime_seventyFourBT_2741 : Nat.Prime 2741 := by norm_num
private theorem prime_seventyFourBT_2791 : Nat.Prime 2791 := by norm_num
private theorem prime_seventyFourBT_2819 : Nat.Prime 2819 := by norm_num
private theorem prime_seventyFourBT_2833 : Nat.Prime 2833 := by norm_num
private theorem prime_seventyFourBT_2971 : Nat.Prime 2971 := by norm_num
private theorem prime_seventyFourBT_3019 : Nat.Prime 3019 := by norm_num
private theorem prime_seventyFourBT_3023 : Nat.Prime 3023 := by norm_num
private theorem prime_seventyFourBT_3319 : Nat.Prime 3319 := by norm_num
private theorem prime_seventyFourBT_3371 : Nat.Prime 3371 := by norm_num
private theorem prime_seventyFourBT_3491 : Nat.Prime 3491 := by norm_num
private theorem prime_seventyFourBT_3583 : Nat.Prime 3583 := by norm_num
private theorem prime_seventyFourBT_3673 : Nat.Prime 3673 := by norm_num
private theorem prime_seventyFourBT_3677 : Nat.Prime 3677 := by norm_num
private theorem prime_seventyFourBT_3727 : Nat.Prime 3727 := by norm_num
private theorem prime_seventyFourBT_3761 : Nat.Prime 3761 := by norm_num
private theorem prime_seventyFourBT_3851 : Nat.Prime 3851 := by norm_num
private theorem prime_seventyFourBT_4049 : Nat.Prime 4049 := by norm_num
private theorem prime_seventyFourBT_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_seventyFourBT_4289 : Nat.Prime 4289 := by norm_num
private theorem prime_seventyFourBT_4397 : Nat.Prime 4397 := by norm_num
private theorem prime_seventyFourBT_4421 : Nat.Prime 4421 := by norm_num
private theorem prime_seventyFourBT_4517 : Nat.Prime 4517 := by norm_num
private theorem prime_seventyFourBT_4657 : Nat.Prime 4657 := by norm_num
private theorem prime_seventyFourBT_4813 : Nat.Prime 4813 := by norm_num
private theorem prime_seventyFourBT_4831 : Nat.Prime 4831 := by norm_num
private theorem prime_seventyFourBT_4951 : Nat.Prime 4951 := by norm_num
private theorem prime_seventyFourBT_4987 : Nat.Prime 4987 := by norm_num
private theorem prime_seventyFourBT_5059 : Nat.Prime 5059 := by norm_num
private theorem prime_seventyFourBT_5167 : Nat.Prime 5167 := by norm_num
private theorem prime_seventyFourBT_5279 : Nat.Prime 5279 := by norm_num
private theorem prime_seventyFourBT_5393 : Nat.Prime 5393 := by norm_num
private theorem prime_seventyFourBT_5417 : Nat.Prime 5417 := by norm_num
private theorem prime_seventyFourBT_5477 : Nat.Prime 5477 := by norm_num
private theorem prime_seventyFourBT_5501 : Nat.Prime 5501 := by norm_num
private theorem prime_seventyFourBT_5591 : Nat.Prime 5591 := by norm_num
private theorem prime_seventyFourBT_6173 : Nat.Prime 6173 := by norm_num
private theorem prime_seventyFourBT_6691 : Nat.Prime 6691 := by norm_num
private theorem prime_seventyFourBT_6857 : Nat.Prime 6857 := by norm_num
private theorem prime_seventyFourBT_6863 : Nat.Prime 6863 := by norm_num
private theorem prime_seventyFourBT_6967 : Nat.Prime 6967 := by norm_num
private theorem prime_seventyFourBT_7213 : Nat.Prime 7213 := by norm_num
private theorem prime_seventyFourBT_7243 : Nat.Prime 7243 := by norm_num
private theorem prime_seventyFourBT_7603 : Nat.Prime 7603 := by norm_num
private theorem prime_seventyFourBT_7793 : Nat.Prime 7793 := by norm_num
private theorem prime_seventyFourBT_8111 : Nat.Prime 8111 := by norm_num
private theorem prime_seventyFourBT_8461 : Nat.Prime 8461 := by norm_num
private theorem prime_seventyFourBT_8849 : Nat.Prime 8849 := by norm_num
private theorem prime_seventyFourBT_9049 : Nat.Prime 9049 := by norm_num
private theorem prime_seventyFourBT_9281 : Nat.Prime 9281 := by norm_num
private theorem prime_seventyFourBT_9689 : Nat.Prime 9689 := by norm_num
private theorem prime_seventyFourBT_9769 : Nat.Prime 9769 := by norm_num
private theorem prime_seventyFourBT_10169 : Nat.Prime 10169 := by norm_num
private theorem prime_seventyFourBT_10333 : Nat.Prime 10333 := by norm_num
private theorem prime_seventyFourBT_10513 : Nat.Prime 10513 := by norm_num
private theorem prime_seventyFourBT_10607 : Nat.Prime 10607 := by norm_num
private theorem prime_seventyFourBT_10663 : Nat.Prime 10663 := by norm_num
private theorem prime_seventyFourBT_11471 : Nat.Prime 11471 := by norm_num
private theorem prime_seventyFourBT_11927 : Nat.Prime 11927 := by norm_num
private theorem prime_seventyFourBT_12541 : Nat.Prime 12541 := by norm_num
private theorem prime_seventyFourBT_12653 : Nat.Prime 12653 := by norm_num
private theorem prime_seventyFourBT_12899 : Nat.Prime 12899 := by norm_num
private theorem prime_seventyFourBT_12907 : Nat.Prime 12907 := by norm_num
private theorem prime_seventyFourBT_13043 : Nat.Prime 13043 := by norm_num
private theorem prime_seventyFourBT_13127 : Nat.Prime 13127 := by norm_num
private theorem prime_seventyFourBT_13177 : Nat.Prime 13177 := by norm_num
private theorem prime_seventyFourBT_13367 : Nat.Prime 13367 := by norm_num
private theorem prime_seventyFourBT_14771 : Nat.Prime 14771 := by norm_num
private theorem prime_seventyFourBT_14783 : Nat.Prime 14783 := by norm_num
private theorem prime_seventyFourBT_14797 : Nat.Prime 14797 := by norm_num
private theorem prime_seventyFourBT_15359 : Nat.Prime 15359 := by norm_num
private theorem prime_seventyFourBT_15383 : Nat.Prime 15383 := by norm_num
private theorem prime_seventyFourBT_15451 : Nat.Prime 15451 := by norm_num
private theorem prime_seventyFourBT_16141 : Nat.Prime 16141 := by norm_num
private theorem prime_seventyFourBT_16883 : Nat.Prime 16883 := by norm_num
private theorem prime_seventyFourBT_17417 : Nat.Prime 17417 := by norm_num
private theorem prime_seventyFourBT_17627 : Nat.Prime 17627 := by norm_num
private theorem prime_seventyFourBT_18553 : Nat.Prime 18553 := by norm_num
private theorem prime_seventyFourBT_19231 : Nat.Prime 19231 := by norm_num
private theorem prime_seventyFourBT_19267 : Nat.Prime 19267 := by norm_num
private theorem prime_seventyFourBT_19927 : Nat.Prime 19927 := by norm_num
private theorem prime_seventyFourBT_21227 : Nat.Prime 21227 := by norm_num
private theorem prime_seventyFourBT_21817 : Nat.Prime 21817 := by norm_num
private theorem prime_seventyFourBT_22157 : Nat.Prime 22157 := by norm_num
private theorem prime_seventyFourBT_22807 : Nat.Prime 22807 := by norm_num
private theorem prime_seventyFourBT_23063 : Nat.Prime 23063 := by norm_num
private theorem prime_seventyFourBT_23173 : Nat.Prime 23173 := by norm_num
private theorem prime_seventyFourBT_23609 : Nat.Prime 23609 := by norm_num
private theorem prime_seventyFourBT_24107 : Nat.Prime 24107 := by norm_num
private theorem prime_seventyFourBT_24113 : Nat.Prime 24113 := by norm_num
private theorem prime_seventyFourBT_24181 : Nat.Prime 24181 := by norm_num
private theorem prime_seventyFourBT_24697 : Nat.Prime 24697 := by norm_num
private theorem prime_seventyFourBT_25301 : Nat.Prime 25301 := by norm_num
private theorem prime_seventyFourBT_26723 : Nat.Prime 26723 := by norm_num
private theorem prime_seventyFourBT_26951 : Nat.Prime 26951 := by norm_num
private theorem prime_seventyFourBT_27827 : Nat.Prime 27827 := by norm_num
private theorem prime_seventyFourBT_29587 : Nat.Prime 29587 := by norm_num
private theorem prime_seventyFourBT_30323 : Nat.Prime 30323 := by norm_num
private theorem prime_seventyFourBT_30557 : Nat.Prime 30557 := by norm_num
private theorem prime_seventyFourBT_31513 : Nat.Prime 31513 := by norm_num
private theorem prime_seventyFourBT_32027 : Nat.Prime 32027 := by norm_num
private theorem prime_seventyFourBT_33563 : Nat.Prime 33563 := by norm_num
private theorem prime_seventyFourBT_34603 : Nat.Prime 34603 := by norm_num
private theorem prime_seventyFourBT_35083 : Nat.Prime 35083 := by norm_num
private theorem prime_seventyFourBT_36749 : Nat.Prime 36749 := by norm_num
private theorem prime_seventyFourBT_39551 : Nat.Prime 39551 := by norm_num
private theorem prime_seventyFourBT_40163 : Nat.Prime 40163 := by norm_num
private theorem prime_seventyFourBT_41597 : Nat.Prime 41597 := by norm_num
private theorem prime_seventyFourBT_42013 : Nat.Prime 42013 := by norm_num
private theorem prime_seventyFourBT_42407 : Nat.Prime 42407 := by norm_num
private theorem prime_seventyFourBT_42491 : Nat.Prime 42491 := by norm_num
private theorem prime_seventyFourBT_45553 : Nat.Prime 45553 := by norm_num
private theorem prime_seventyFourBT_49697 : Nat.Prime 49697 := by norm_num
private theorem prime_seventyFourBT_53819 : Nat.Prime 53819 := by norm_num
private theorem prime_seventyFourBT_54559 : Nat.Prime 54559 := by norm_num
private theorem prime_seventyFourBT_54727 : Nat.Prime 54727 := by norm_num
private theorem prime_seventyFourBT_59627 : Nat.Prime 59627 := by norm_num
private theorem prime_seventyFourBT_59879 : Nat.Prime 59879 := by norm_num
private theorem prime_seventyFourBT_61027 : Nat.Prime 61027 := by norm_num
private theorem prime_seventyFourBT_61231 : Nat.Prime 61231 := by norm_num
private theorem prime_seventyFourBT_61657 : Nat.Prime 61657 := by norm_num
private theorem prime_seventyFourBT_63467 : Nat.Prime 63467 := by norm_num
private theorem prime_seventyFourBT_68927 : Nat.Prime 68927 := by norm_num
private theorem prime_seventyFourBT_73091 : Nat.Prime 73091 := by norm_num
private theorem prime_seventyFourBT_74797 : Nat.Prime 74797 := by norm_num
private theorem prime_seventyFourBT_76367 : Nat.Prime 76367 := by norm_num
private theorem prime_seventyFourBT_77863 : Nat.Prime 77863 := by norm_num
private theorem prime_seventyFourBT_81001 : Nat.Prime 81001 := by norm_num
private theorem prime_seventyFourBT_81077 : Nat.Prime 81077 := by norm_num
private theorem prime_seventyFourBT_82037 : Nat.Prime 82037 := by norm_num
private theorem prime_seventyFourBT_84481 : Nat.Prime 84481 := by norm_num
private theorem prime_seventyFourBT_85531 : Nat.Prime 85531 := by norm_num
private theorem prime_seventyFourBT_89917 : Nat.Prime 89917 := by norm_num
private theorem prime_seventyFourBT_90017 : Nat.Prime 90017 := by norm_num
private theorem prime_seventyFourBT_93377 : Nat.Prime 93377 := by norm_num
private theorem prime_seventyFourBT_93629 : Nat.Prime 93629 := by norm_num
private theorem prime_seventyFourBT_97879 : Nat.Prime 97879 := by norm_num
private theorem prime_seventyFourBT_107843 : Nat.Prime 107843 := by norm_num
private theorem prime_seventyFourBT_116747 : Nat.Prime 116747 := by norm_num
private theorem prime_seventyFourBT_117703 : Nat.Prime 117703 := by norm_num
private theorem prime_seventyFourBT_129967 : Nat.Prime 129967 := by norm_num
private theorem prime_seventyFourBT_131497 : Nat.Prime 131497 := by norm_num
private theorem prime_seventyFourBT_135433 : Nat.Prime 135433 := by norm_num
private theorem prime_seventyFourBT_137483 : Nat.Prime 137483 := by norm_num
private theorem prime_seventyFourBT_137623 : Nat.Prime 137623 := by norm_num
private theorem prime_seventyFourBT_149551 : Nat.Prime 149551 := by norm_num
private theorem prime_seventyFourBT_156467 : Nat.Prime 156467 := by norm_num
private theorem prime_seventyFourBT_160207 : Nat.Prime 160207 := by norm_num
private theorem prime_seventyFourBT_170537 : Nat.Prime 170537 := by norm_num
private theorem prime_seventyFourBT_175759 : Nat.Prime 175759 := by norm_num
private theorem prime_seventyFourBT_186191 : Nat.Prime 186191 := by norm_num
private theorem prime_seventyFourBT_192917 : Nat.Prime 192917 := by norm_num
private theorem prime_seventyFourBT_198833 : Nat.Prime 198833 := by norm_num
private theorem prime_seventyFourBT_199583 : Nat.Prime 199583 := by norm_num
private theorem prime_seventyFourBT_204431 : Nat.Prime 204431 := by norm_num
private theorem prime_seventyFourBT_204667 : Nat.Prime 204667 := by norm_num
private theorem prime_seventyFourBT_204803 : Nat.Prime 204803 := by norm_num
private theorem prime_seventyFourBT_204821 : Nat.Prime 204821 := by norm_num
private theorem prime_seventyFourBT_206351 : Nat.Prime 206351 := by norm_num
private theorem prime_seventyFourBT_220681 : Nat.Prime 220681 := by norm_num
private theorem prime_seventyFourBT_223403 : Nat.Prime 223403 := by norm_num
private theorem prime_seventyFourBT_241979 : Nat.Prime 241979 := by norm_num
private theorem prime_seventyFourBT_251197 : Nat.Prime 251197 := by norm_num
private theorem prime_seventyFourBT_257519 : Nat.Prime 257519 := by norm_num
private theorem prime_seventyFourBT_262651 : Nat.Prime 262651 := by norm_num
private theorem prime_seventyFourBT_265141 : Nat.Prime 265141 := by norm_num
private theorem prime_seventyFourBT_286801 : Nat.Prime 286801 := by norm_num
private theorem prime_seventyFourBT_316363 : Nat.Prime 316363 := by norm_num
private theorem prime_seventyFourBT_331217 : Nat.Prime 331217 := by norm_num
private theorem prime_seventyFourBT_354323 : Nat.Prime 354323 := by norm_num
private theorem prime_seventyFourBT_358993 : Nat.Prime 358993 := by norm_num
private theorem prime_seventyFourBT_372773 : Nat.Prime 372773 := by norm_num
private theorem prime_seventyFourBT_372859 : Nat.Prime 372859 := by norm_num
private theorem prime_seventyFourBT_389539 : Nat.Prime 389539 := by norm_num
private theorem prime_seventyFourBT_402313 : Nat.Prime 402313 := by norm_num
private theorem prime_seventyFourBT_408769 : Nat.Prime 408769 := by norm_num
private theorem prime_seventyFourBT_411703 : Nat.Prime 411703 := by norm_num
private theorem prime_seventyFourBT_446827 : Nat.Prime 446827 := by norm_num
private theorem prime_seventyFourBT_466139 : Nat.Prime 466139 := by norm_num
private theorem prime_seventyFourBT_543149 : Nat.Prime 543149 := by norm_num
private theorem prime_seventyFourBT_589811 : Nat.Prime 589811 := by norm_num
private theorem prime_seventyFourBT_608611 : Nat.Prime 608611 := by norm_num
private theorem prime_seventyFourBT_618883 : Nat.Prime 618883 := by norm_num
private theorem prime_seventyFourBT_633569 : Nat.Prime 633569 := by norm_num
private theorem prime_seventyFourBT_636061 : Nat.Prime 636061 := by norm_num
private theorem prime_seventyFourBT_651109 : Nat.Prime 651109 := by norm_num
private theorem prime_seventyFourBT_699197 : Nat.Prime 699197 := by norm_num
private theorem prime_seventyFourBT_708913 : Nat.Prime 708913 := by norm_num
private theorem prime_seventyFourBT_718453 : Nat.Prime 718453 := by norm_num
private theorem prime_seventyFourBT_718717 : Nat.Prime 718717 := by norm_num
private theorem prime_seventyFourBT_720211 : Nat.Prime 720211 := by norm_num
private theorem prime_seventyFourBT_794071 : Nat.Prime 794071 := by norm_num
private theorem prime_seventyFourBT_963173 : Nat.Prime 963173 := by norm_num
private theorem prime_seventyFourBT_968273 : Nat.Prime 968273 := by norm_num
private theorem prime_seventyFourBT_1063273 : Nat.Prime 1063273 := by norm_num
private theorem prime_seventyFourBT_1271929 : Nat.Prime 1271929 := by norm_num
private theorem prime_seventyFourBT_1314233 : Nat.Prime 1314233 := by norm_num
private theorem prime_seventyFourBT_1354819 : Nat.Prime 1354819 := by norm_num
private theorem prime_seventyFourBT_1421711 : Nat.Prime 1421711 := by norm_num
private theorem prime_seventyFourBT_1563077 : Nat.Prime 1563077 := by norm_num
private theorem prime_seventyFourBT_1569637 : Nat.Prime 1569637 := by norm_num
private theorem prime_seventyFourBT_1646947 : Nat.Prime 1646947 := by norm_num
private theorem prime_seventyFourBT_1697053 : Nat.Prime 1697053 := by norm_num
private theorem prime_seventyFourBT_1754653 : Nat.Prime 1754653 := by norm_num
private theorem prime_seventyFourBT_1891433 : Nat.Prime 1891433 := by norm_num
private theorem prime_seventyFourBT_1900049 : Nat.Prime 1900049 := by norm_num
private theorem prime_seventyFourBT_1912847 : Nat.Prime 1912847 := by norm_num
private theorem prime_seventyFourBT_2052989 : Nat.Prime 2052989 := by norm_num
private theorem prime_seventyFourBT_2088679 : Nat.Prime 2088679 := by norm_num
private theorem prime_seventyFourBT_2192129 : Nat.Prime 2192129 := by norm_num
private theorem prime_seventyFourBT_2289181 : Nat.Prime 2289181 := by norm_num
private theorem prime_seventyFourBT_2304011 : Nat.Prime 2304011 := by norm_num
private theorem prime_seventyFourBT_2346959 : Nat.Prime 2346959 := by norm_num
private theorem prime_seventyFourBT_2397091 : Nat.Prime 2397091 := by norm_num
private theorem prime_seventyFourBT_2442179 : Nat.Prime 2442179 := by norm_num
private theorem prime_seventyFourBT_3148051 : Nat.Prime 3148051 := by norm_num
private theorem prime_seventyFourBT_3297353 : Nat.Prime 3297353 := by norm_num
private theorem prime_seventyFourBT_3306707 : Nat.Prime 3306707 := by norm_num
private theorem prime_seventyFourBT_3368593 : Nat.Prime 3368593 := by norm_num
private theorem prime_seventyFourBT_3410681 : Nat.Prime 3410681 := by norm_num
private theorem prime_seventyFourBT_3417671 : Nat.Prime 3417671 := by norm_num
private theorem prime_seventyFourBT_3468511 : Nat.Prime 3468511 := by norm_num
private theorem prime_seventyFourBT_3578903 : Nat.Prime 3578903 := by norm_num
private theorem prime_seventyFourBT_3650651 : Nat.Prime 3650651 := by norm_num
private theorem prime_seventyFourBT_3697033 : Nat.Prime 3697033 := by norm_num
private theorem prime_seventyFourBT_3714323 : Nat.Prime 3714323 := by norm_num
private theorem prime_seventyFourBT_3780599 : Nat.Prime 3780599 := by norm_num
private theorem prime_seventyFourBT_3788273 : Nat.Prime 3788273 := by norm_num
private theorem prime_seventyFourBT_3901787 : Nat.Prime 3901787 := by norm_num
private theorem prime_seventyFourBT_4146547 : Nat.Prime 4146547 := by norm_num
private theorem prime_seventyFourBT_4177309 : Nat.Prime 4177309 := by norm_num
private theorem prime_seventyFourBT_4224167 : Nat.Prime 4224167 := by norm_num
private theorem prime_seventyFourBT_4433633 : Nat.Prime 4433633 := by norm_num
private theorem prime_seventyFourBT_4806713 : Nat.Prime 4806713 := by norm_num
private theorem prime_seventyFourBT_4895207 : Nat.Prime 4895207 := by norm_num
private theorem prime_seventyFourBT_4906907 : Nat.Prime 4906907 := by norm_num
private theorem prime_seventyFourBT_4984883 : Nat.Prime 4984883 := by norm_num
private theorem prime_seventyFourBT_5358833 : Nat.Prime 5358833 := by norm_num
private theorem prime_seventyFourBT_5545789 : Nat.Prime 5545789 := by norm_num
private theorem prime_seventyFourBT_5830193 : Nat.Prime 5830193 := by norm_num
private theorem prime_seventyFourBT_6124253 : Nat.Prime 6124253 := by norm_num
private theorem prime_seventyFourBT_6456881 : Nat.Prime 6456881 := by norm_num
private theorem prime_seventyFourBT_6660221 : Nat.Prime 6660221 := by norm_num
private theorem prime_seventyFourBT_6840083 : Nat.Prime 6840083 := by norm_num
private theorem prime_seventyFourBT_6856279 : Nat.Prime 6856279 := by norm_num
private theorem prime_seventyFourBT_6884639 : Nat.Prime 6884639 := by norm_num
private theorem prime_seventyFourBT_6901637 : Nat.Prime 6901637 := by norm_num
private theorem prime_seventyFourBT_6976421 : Nat.Prime 6976421 := by norm_num
private theorem prime_seventyFourBT_7078699 : Nat.Prime 7078699 := by norm_num
private theorem prime_seventyFourBT_7432753 : Nat.Prime 7432753 := by norm_num
private theorem prime_seventyFourBT_7496623 : Nat.Prime 7496623 := by norm_num
private theorem prime_seventyFourBT_8126303 : Nat.Prime 8126303 := by norm_num
private theorem prime_seventyFourBT_8299091 : Nat.Prime 8299091 := by norm_num
private theorem prime_seventyFourBT_8485801 : Nat.Prime 8485801 := by norm_num
private theorem prime_seventyFourBT_8802181 : Nat.Prime 8802181 := by norm_num
private theorem prime_seventyFourBT_8806613 : Nat.Prime 8806613 := by norm_num
private theorem prime_seventyFourBT_9350729 : Nat.Prime 9350729 := by norm_num
private theorem prime_seventyFourBT_9579809 : Nat.Prime 9579809 := by norm_num
private theorem prime_seventyFourBT_9657163 : Nat.Prime 9657163 := by norm_num
private theorem prime_seventyFourBT_9997129 : Nat.Prime 9997129 := by norm_num
private theorem prime_seventyFourBT_10950871 : Nat.Prime 10950871 := by norm_num
private theorem prime_seventyFourBT_11094553 : Nat.Prime 11094553 := by norm_num
private theorem prime_seventyFourBT_11335327 : Nat.Prime 11335327 := by norm_num
private theorem prime_seventyFourBT_11906429 : Nat.Prime 11906429 := by norm_num
private theorem prime_seventyFourBT_12310733 : Nat.Prime 12310733 := by norm_num
private theorem prime_seventyFourBT_12861983 : Nat.Prime 12861983 := by norm_num
private theorem prime_seventyFourBT_12969857 : Nat.Prime 12969857 := by norm_num
private theorem prime_seventyFourBT_13622341 : Nat.Prime 13622341 := by norm_num
private theorem prime_seventyFourBT_13918609 : Nat.Prime 13918609 := by norm_num
private theorem prime_seventyFourBT_14096023 : Nat.Prime 14096023 := by norm_num
private theorem prime_seventyFourBT_15229531 : Nat.Prime 15229531 := by norm_num
private theorem prime_seventyFourBT_15555307 : Nat.Prime 15555307 := by norm_num
private theorem prime_seventyFourBT_16294513 : Nat.Prime 16294513 := by norm_num
private theorem prime_seventyFourBT_16925663 : Nat.Prime 16925663 := by norm_num
private theorem prime_seventyFourBT_17803967 : Nat.Prime 17803967 := by norm_num
private theorem prime_seventyFourBT_18500591 : Nat.Prime 18500591 := by norm_num
private theorem prime_seventyFourBT_19592581 : Nat.Prime 19592581 := by norm_num
private theorem prime_seventyFourBT_20131571 : Nat.Prime 20131571 := by norm_num
private theorem prime_seventyFourBT_20568937 : Nat.Prime 20568937 := by norm_num
private theorem prime_seventyFourBT_21783071 : Nat.Prime 21783071 := by norm_num
private theorem prime_seventyFourBT_21885317 : Nat.Prime 21885317 := by norm_num
private theorem prime_seventyFourBT_22727609 : Nat.Prime 22727609 := by norm_num
private theorem prime_seventyFourBT_23521621 : Nat.Prime 23521621 := by norm_num
private theorem prime_seventyFourBT_26321693 : Nat.Prime 26321693 := by norm_num
private theorem prime_seventyFourBT_26771861 : Nat.Prime 26771861 := by norm_num
private theorem prime_seventyFourBT_27712931 : Nat.Prime 27712931 := by norm_num
private theorem prime_seventyFourBT_29815703 : Nat.Prime 29815703 := by norm_num
private theorem prime_seventyFourBT_36891539 : Nat.Prime 36891539 := by
  apply lucas_primality 36891539 (2 : ZMod 36891539)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (636061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (636061, 1)] : List FactorBlock).map factorBlockValue).prod) = 36891539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_29
      · exact prime_seventyFourBT_636061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36891539) ^ 18445769 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 36891539) ^ 1272122 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 36891539) ^ 58 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_37125547 : Nat.Prime 37125547 := by
  apply lucas_primality 37125547 (3 : ZMod 37125547)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (116747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (116747, 1)] : List FactorBlock).map factorBlockValue).prod) = 37125547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_53
      · exact prime_seventyFourBT_116747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37125547) ^ 18562773 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 37125547) ^ 12375182 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 37125547) ^ 700482 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 37125547) ^ 318 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_40024267 : Nat.Prime 40024267 := by
  apply lucas_primality 40024267 (2 : ZMod 40024267)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (383, 1), (17417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (383, 1), (17417, 1)] : List FactorBlock).map factorBlockValue).prod) = 40024267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_383
      · exact prime_seventyFourBT_17417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40024267) ^ 20012133 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 40024267) ^ 13341422 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 40024267) ^ 104502 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 40024267) ^ 2298 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_45613013 : Nat.Prime 45613013 := by
  apply lucas_primality 45613013 (2 : ZMod 45613013)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 1), (233, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 1), (233, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) = 45613013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_109
      · exact prime_seventyFourBT_233
      · exact prime_seventyFourBT_449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45613013) ^ 22806506 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 45613013) ^ 418468 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 45613013) ^ 195764 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 45613013) ^ 101588 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_46939181 : Nat.Prime 46939181 := by
  apply lucas_primality 46939181 (3 : ZMod 46939181)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2346959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2346959, 1)] : List FactorBlock).map factorBlockValue).prod) = 46939181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_2346959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 46939181) ^ 23469590 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 46939181) ^ 9387836 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 46939181) ^ 20 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_53599549 : Nat.Prime 53599549 := by
  apply lucas_primality 53599549 (2 : ZMod 53599549)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (461, 1), (9689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (461, 1), (9689, 1)] : List FactorBlock).map factorBlockValue).prod) = 53599549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_461
      · exact prime_seventyFourBT_9689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53599549) ^ 26799774 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 53599549) ^ 17866516 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 53599549) ^ 116268 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 53599549) ^ 5532 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_54310033 : Nat.Prime 54310033 := by
  apply lucas_primality 54310033 (5 : ZMod 54310033)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 2), (43, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 2), (43, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) = 54310033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_43
      · exact prime_seventyFourBT_179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 54310033) ^ 27155016 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 54310033) ^ 18103344 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 54310033) ^ 7758576 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 54310033) ^ 1263024 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 54310033) ^ 303408 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_56384093 : Nat.Prime 56384093 := by
  apply lucas_primality 56384093 (2 : ZMod 56384093)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (14096023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (14096023, 1)] : List FactorBlock).map factorBlockValue).prod) = 56384093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_14096023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 56384093) ^ 28192046 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 56384093) ^ 4 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_57285587 : Nat.Prime 57285587 := by
  apply lucas_primality 57285587 (2 : ZMod 57285587)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (307, 1), (1181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (307, 1), (1181, 1)] : List FactorBlock).map factorBlockValue).prod) = 57285587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_79
      · exact prime_seventyFourBT_307
      · exact prime_seventyFourBT_1181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57285587) ^ 28642793 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 57285587) ^ 725134 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 57285587) ^ 186598 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 57285587) ^ 48506 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_61526981 : Nat.Prime 61526981 := by
  apply lucas_primality 61526981 (2 : ZMod 61526981)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (43, 1), (2467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (43, 1), (2467, 1)] : List FactorBlock).map factorBlockValue).prod) = 61526981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_29
      · exact prime_seventyFourBT_43
      · exact prime_seventyFourBT_2467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 61526981) ^ 30763490 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 61526981) ^ 12305396 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 61526981) ^ 2121620 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 61526981) ^ 1430860 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 61526981) ^ 24940 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_62433199 : Nat.Prime 62433199 := by
  apply lucas_primality 62433199 (3 : ZMod 62433199)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3468511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3468511, 1)] : List FactorBlock).map factorBlockValue).prod) = 62433199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_3468511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 62433199) ^ 31216599 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 62433199) ^ 20811066 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 62433199) ^ 18 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_71059283 : Nat.Prime 71059283 := by
  apply lucas_primality 71059283 (2 : ZMod 71059283)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (220681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (220681, 1)] : List FactorBlock).map factorBlockValue).prod) = 71059283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_23
      · exact prime_seventyFourBT_220681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 71059283) ^ 35529641 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 71059283) ^ 10151326 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 71059283) ^ 3089534 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 71059283) ^ 322 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_73783079 : Nat.Prime 73783079 := by
  apply lucas_primality 73783079 (13 : ZMod 73783079)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (36891539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (36891539, 1)] : List FactorBlock).map factorBlockValue).prod) = 73783079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_36891539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 73783079) ^ 36891539 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 73783079) ^ 2 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_77869859 : Nat.Prime 77869859 := by
  apply lucas_primality 77869859 (2 : ZMod 77869859)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 2), (6691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 2), (6691, 1)] : List FactorBlock).map factorBlockValue).prod) = 77869859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_23
      · exact prime_seventyFourBT_6691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 77869859) ^ 38934929 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 77869859) ^ 7079078 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 77869859) ^ 3385646 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 77869859) ^ 11638 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_80057017 : Nat.Prime 80057017 := by
  apply lucas_primality 80057017 (7 : ZMod 80057017)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (85531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (85531, 1)] : List FactorBlock).map factorBlockValue).prod) = 80057017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_85531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 80057017) ^ 40028508 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 80057017) ^ 26685672 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 80057017) ^ 6158232 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 80057017) ^ 936 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_84004363 : Nat.Prime 84004363 := by
  apply lucas_primality 84004363 (3 : ZMod 84004363)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (358993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (358993, 1)] : List FactorBlock).map factorBlockValue).prod) = 84004363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_358993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 84004363) ^ 42002181 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 84004363) ^ 28001454 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 84004363) ^ 6461874 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 84004363) ^ 234 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_97969601 : Nat.Prime 97969601 := by
  apply lucas_primality 97969601 (3 : ZMod 97969601)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 2), (61231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 2), (61231, 1)] : List FactorBlock).map factorBlockValue).prod) = 97969601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_61231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 97969601) ^ 48984800 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 97969601) ^ 19593920 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 97969601) ^ 1600 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_106407193 : Nat.Prime 106407193 := by
  apply lucas_primality 106407193 (5 : ZMod 106407193)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4433633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4433633, 1)] : List FactorBlock).map factorBlockValue).prod) = 106407193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_4433633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 106407193) ^ 53203596 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 106407193) ^ 35469064 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 106407193) ^ 24 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_117141499 : Nat.Prime 117141499 := by
  apply lucas_primality 117141499 (2 : ZMod 117141499)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 1), (29, 1), (31, 1), (127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 1), (29, 1), (31, 1), (127, 1)] : List FactorBlock).map factorBlockValue).prod) = 117141499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_19
      · exact prime_seventyFourBT_29
      · exact prime_seventyFourBT_31
      · exact prime_seventyFourBT_127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 117141499) ^ 58570749 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 117141499) ^ 39047166 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 117141499) ^ 6165342 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 117141499) ^ 4039362 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 117141499) ^ 3778758 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 117141499) ^ 922374 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_123053963 : Nat.Prime 123053963 := by
  apply lucas_primality 123053963 (2 : ZMod 123053963)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61526981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61526981, 1)] : List FactorBlock).map factorBlockValue).prod) = 123053963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_61526981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 123053963) ^ 61526981 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 123053963) ^ 2 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_139924633 : Nat.Prime 139924633 := by
  apply lucas_primality 139924633 (5 : ZMod 139924633)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5830193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5830193, 1)] : List FactorBlock).map factorBlockValue).prod) = 139924633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5830193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 139924633) ^ 69962316 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 139924633) ^ 46641544 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 139924633) ^ 24 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_170081029 : Nat.Prime 170081029 := by
  apply lucas_primality 170081029 (2 : ZMod 170081029)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (53, 1), (6857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (53, 1), (6857, 1)] : List FactorBlock).map factorBlockValue).prod) = 170081029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_53
      · exact prime_seventyFourBT_6857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 170081029) ^ 85040514 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 170081029) ^ 56693676 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 170081029) ^ 13083156 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 170081029) ^ 3209076 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 170081029) ^ 24804 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_183671503 : Nat.Prime 183671503 := by
  apply lucas_primality 183671503 (5 : ZMod 183671503)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (17, 1), (36749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (17, 1), (36749, 1)] : List FactorBlock).map factorBlockValue).prod) = 183671503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_17
      · exact prime_seventyFourBT_36749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 183671503) ^ 91835751 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 183671503) ^ 61223834 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 183671503) ^ 26238786 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 183671503) ^ 10804206 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 183671503) ^ 4998 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_185763833 : Nat.Prime 185763833 := by
  apply lucas_primality 185763833 (3 : ZMod 185763833)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (71, 1), (359, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (71, 1), (359, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) = 185763833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_71
      · exact prime_seventyFourBT_359
      · exact prime_seventyFourBT_911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 185763833) ^ 92881916 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 185763833) ^ 2616392 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 185763833) ^ 517448 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 185763833) ^ 203912 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_185781119 : Nat.Prime 185781119 := by
  apply lucas_primality 185781119 (29 : ZMod 185781119)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1193, 1), (77863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1193, 1), (77863, 1)] : List FactorBlock).map factorBlockValue).prod) = 185781119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_1193
      · exact prime_seventyFourBT_77863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (29 : ZMod 185781119) ^ 92890559 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (29 : ZMod 185781119) ^ 155726 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (29 : ZMod 185781119) ^ 2386 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_190489963 : Nat.Prime 190489963 := by
  apply lucas_primality 190489963 (2 : ZMod 190489963)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (2442179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (2442179, 1)] : List FactorBlock).map factorBlockValue).prod) = 190489963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_2442179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 190489963) ^ 95244981 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 190489963) ^ 63496654 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 190489963) ^ 14653074 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 190489963) ^ 78 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_192313967 : Nat.Prime 192313967 := by
  apply lucas_primality 192313967 (10 : ZMod 192313967)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (79, 1), (93629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (79, 1), (93629, 1)] : List FactorBlock).map factorBlockValue).prod) = 192313967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_79
      · exact prime_seventyFourBT_93629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 192313967) ^ 96156983 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 192313967) ^ 14793382 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 192313967) ^ 2434354 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 192313967) ^ 2054 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_197601193 : Nat.Prime 197601193 := by
  apply lucas_primality 197601193 (15 : ZMod 197601193)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (31, 1), (223, 1), (397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (31, 1), (223, 1), (397, 1)] : List FactorBlock).map factorBlockValue).prod) = 197601193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_31
      · exact prime_seventyFourBT_223
      · exact prime_seventyFourBT_397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 197601193) ^ 98800596 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (15 : ZMod 197601193) ^ 65867064 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (15 : ZMod 197601193) ^ 6374232 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (15 : ZMod 197601193) ^ 886104 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (15 : ZMod 197601193) ^ 497736 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_209042681 : Nat.Prime 209042681 := by
  apply lucas_primality 209042681 (3 : ZMod 209042681)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (11, 1), (67, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (11, 1), (67, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) = 209042681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_67
      · exact prime_seventyFourBT_1013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 209042681) ^ 104521340 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 209042681) ^ 41808536 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 209042681) ^ 29863240 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 209042681) ^ 19003880 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 209042681) ^ 3120040 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 209042681) ^ 206360 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_229902889 : Nat.Prime 229902889 := by
  apply lucas_primality 229902889 (7 : ZMod 229902889)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (167, 1), (3019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (167, 1), (3019, 1)] : List FactorBlock).map factorBlockValue).prod) = 229902889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_19
      · exact prime_seventyFourBT_167
      · exact prime_seventyFourBT_3019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 229902889) ^ 114951444 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 229902889) ^ 76634296 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 229902889) ^ 12100152 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 229902889) ^ 1376664 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 229902889) ^ 76152 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_242538697 : Nat.Prime 242538697 := by
  apply lucas_primality 242538697 (5 : ZMod 242538697)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (3368593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (3368593, 1)] : List FactorBlock).map factorBlockValue).prod) = 242538697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_3368593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 242538697) ^ 121269348 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 242538697) ^ 80846232 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 242538697) ^ 72 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_245345351 : Nat.Prime 245345351 := by
  apply lucas_primality 245345351 (11 : ZMod 245345351)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (4906907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (4906907, 1)] : List FactorBlock).map factorBlockValue).prod) = 245345351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_4906907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 245345351) ^ 122672675 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 245345351) ^ 49069070 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 245345351) ^ 50 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_258489761 : Nat.Prime 258489761 := by
  apply lucas_primality 258489761 (3 : ZMod 258489761)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (17, 1), (29, 2), (113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (17, 1), (29, 2), (113, 1)] : List FactorBlock).map factorBlockValue).prod) = 258489761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_17
      · exact prime_seventyFourBT_29
      · exact prime_seventyFourBT_113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 258489761) ^ 129244880 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 258489761) ^ 51697952 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 258489761) ^ 15205280 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 258489761) ^ 8913440 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 258489761) ^ 2287520 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_297338669 : Nat.Prime 297338669 := by
  apply lucas_primality 297338669 (2 : ZMod 297338669)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (211, 1), (32027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (211, 1), (32027, 1)] : List FactorBlock).map factorBlockValue).prod) = 297338669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_211
      · exact prime_seventyFourBT_32027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 297338669) ^ 148669334 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 297338669) ^ 27030788 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 297338669) ^ 1409188 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 297338669) ^ 9284 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_329102993 : Nat.Prime 329102993 := by
  apply lucas_primality 329102993 (3 : ZMod 329102993)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (20568937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (20568937, 1)] : List FactorBlock).map factorBlockValue).prod) = 329102993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_20568937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 329102993) ^ 164551496 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 329102993) ^ 16 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_389635199 : Nat.Prime 389635199 := by
  apply lucas_primality 389635199 (7 : ZMod 389635199)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (1891433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (1891433, 1)] : List FactorBlock).map factorBlockValue).prod) = 389635199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_103
      · exact prime_seventyFourBT_1891433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 389635199) ^ 194817599 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 389635199) ^ 3782866 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 389635199) ^ 206 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_421669351 : Nat.Prime 421669351 := by
  apply lucas_primality 421669351 (3 : ZMod 421669351)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (23, 1), (131, 1), (311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (23, 1), (131, 1), (311, 1)] : List FactorBlock).map factorBlockValue).prod) = 421669351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_23
      · exact prime_seventyFourBT_131
      · exact prime_seventyFourBT_311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 421669351) ^ 210834675 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 421669351) ^ 140556450 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 421669351) ^ 84333870 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 421669351) ^ 18333450 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 421669351) ^ 3218850 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 421669351) ^ 1355850 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_438034841 : Nat.Prime 438034841 := by
  apply lucas_primality 438034841 (7 : ZMod 438034841)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (10950871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (10950871, 1)] : List FactorBlock).map factorBlockValue).prod) = 438034841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_10950871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 438034841) ^ 219017420 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 438034841) ^ 87606968 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 438034841) ^ 40 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_537172931 : Nat.Prime 537172931 := by
  apply lucas_primality 537172931 (2 : ZMod 537172931)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (2087, 1), (3677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (2087, 1), (3677, 1)] : List FactorBlock).map factorBlockValue).prod) = 537172931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_2087
      · exact prime_seventyFourBT_3677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 537172931) ^ 268586465 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 537172931) ^ 107434586 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 537172931) ^ 76738990 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 537172931) ^ 257390 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 537172931) ^ 146090 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_556023077 : Nat.Prime 556023077 := by
  apply lucas_primality 556023077 (2 : ZMod 556023077)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2347, 1), (8461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2347, 1), (8461, 1)] : List FactorBlock).map factorBlockValue).prod) = 556023077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_2347
      · exact prime_seventyFourBT_8461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 556023077) ^ 278011538 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 556023077) ^ 79431868 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 556023077) ^ 236908 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 556023077) ^ 65716 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_559698533 : Nat.Prime 559698533 := by
  apply lucas_primality 559698533 (2 : ZMod 559698533)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139924633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139924633, 1)] : List FactorBlock).map factorBlockValue).prod) = 559698533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_139924633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 559698533) ^ 279849266 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 559698533) ^ 4 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_594677339 : Nat.Prime 594677339 := by
  apply lucas_primality 594677339 (2 : ZMod 594677339)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (297338669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (297338669, 1)] : List FactorBlock).map factorBlockValue).prod) = 594677339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_297338669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 594677339) ^ 297338669 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 594677339) ^ 2 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_658095089 : Nat.Prime 658095089 := by
  apply lucas_primality 658095089 (3 : ZMod 658095089)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 2), (683, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 2), (683, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod) = 658095089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_683
      · exact prime_seventyFourBT_1229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 658095089) ^ 329047544 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 658095089) ^ 94013584 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 658095089) ^ 963536 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 658095089) ^ 535472 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_711957223 : Nat.Prime 711957223 := by
  apply lucas_primality 711957223 (3 : ZMod 711957223)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (31, 1), (47, 1), (9049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (31, 1), (47, 1), (9049, 1)] : List FactorBlock).map factorBlockValue).prod) = 711957223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_31
      · exact prime_seventyFourBT_47
      · exact prime_seventyFourBT_9049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 711957223) ^ 355978611 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 711957223) ^ 237319074 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 711957223) ^ 22966362 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 711957223) ^ 15148026 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 711957223) ^ 78678 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_730191503 : Nat.Prime 730191503 := by
  apply lucas_primality 730191503 (5 : ZMod 730191503)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (14783, 1), (24697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (14783, 1), (24697, 1)] : List FactorBlock).map factorBlockValue).prod) = 730191503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_14783
      · exact prime_seventyFourBT_24697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 730191503) ^ 365095751 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 730191503) ^ 49394 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 730191503) ^ 29566 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_870916159 : Nat.Prime 870916159 := by
  apply lucas_primality 870916159 (3 : ZMod 870916159)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (2304011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (2304011, 1)] : List FactorBlock).map factorBlockValue).prod) = 870916159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_2304011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 870916159) ^ 435458079 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 870916159) ^ 290305386 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 870916159) ^ 124416594 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 870916159) ^ 378 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_877464491 : Nat.Prime 877464491 := by
  apply lucas_primality 877464491 (2 : ZMod 877464491)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (23, 1), (383, 1), (1423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (23, 1), (383, 1), (1423, 1)] : List FactorBlock).map factorBlockValue).prod) = 877464491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_23
      · exact prime_seventyFourBT_383
      · exact prime_seventyFourBT_1423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 877464491) ^ 438732245 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 877464491) ^ 175492898 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 877464491) ^ 125352070 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 877464491) ^ 38150630 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 877464491) ^ 2291030 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 877464491) ^ 616630 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1119397067 : Nat.Prime 1119397067 := by
  apply lucas_primality 1119397067 (2 : ZMod 1119397067)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (559698533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (559698533, 1)] : List FactorBlock).map factorBlockValue).prod) = 1119397067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_559698533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1119397067) ^ 559698533 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1119397067) ^ 2 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1143361069 : Nat.Prime 1143361069 := by
  apply lucas_primality 1143361069 (6 : ZMod 1143361069)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (179, 1), (487, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (179, 1), (487, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) = 1143361069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_179
      · exact prime_seventyFourBT_487
      · exact prime_seventyFourBT_1093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1143361069) ^ 571680534 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143361069) ^ 381120356 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143361069) ^ 6387492 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143361069) ^ 2347764 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143361069) ^ 1046076 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1321555831 : Nat.Prime 1321555831 := by
  apply lucas_primality 1321555831 (3 : ZMod 1321555831)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (331217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (331217, 1)] : List FactorBlock).map factorBlockValue).prod) = 1321555831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_19
      · exact prime_seventyFourBT_331217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1321555831) ^ 660777915 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1321555831) ^ 440518610 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1321555831) ^ 264311166 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1321555831) ^ 188793690 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1321555831) ^ 69555570 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1321555831) ^ 3990 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1414818131 : Nat.Prime 1414818131 := by
  apply lucas_primality 1414818131 (2 : ZMod 1414818131)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (12861983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (12861983, 1)] : List FactorBlock).map factorBlockValue).prod) = 1414818131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_12861983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1414818131) ^ 707409065 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1414818131) ^ 282963626 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1414818131) ^ 128619830 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1414818131) ^ 110 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1611177559 : Nat.Prime 1611177559 := by
  apply lucas_primality 1611177559 (3 : ZMod 1611177559)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1069, 1), (251197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1069, 1), (251197, 1)] : List FactorBlock).map factorBlockValue).prod) = 1611177559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_1069
      · exact prime_seventyFourBT_251197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1611177559) ^ 805588779 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1611177559) ^ 537059186 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1611177559) ^ 1507182 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1611177559) ^ 6414 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1845439469 : Nat.Prime 1845439469 := by
  apply lucas_primality 1845439469 (2 : ZMod 1845439469)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (479, 1), (963173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (479, 1), (963173, 1)] : List FactorBlock).map factorBlockValue).prod) = 1845439469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_479
      · exact prime_seventyFourBT_963173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1845439469) ^ 922719734 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1845439469) ^ 3852692 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1845439469) ^ 1916 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1879259801 : Nat.Prime 1879259801 := by
  apply lucas_primality 1879259801 (3 : ZMod 1879259801)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (11, 1), (421, 1), (2029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (11, 1), (421, 1), (2029, 1)] : List FactorBlock).map factorBlockValue).prod) = 1879259801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_421
      · exact prime_seventyFourBT_2029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1879259801) ^ 939629900 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1879259801) ^ 375851960 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1879259801) ^ 170841800 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1879259801) ^ 4463800 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1879259801) ^ 926200 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_2251181059 : Nat.Prime 2251181059 := by
  apply lucas_primality 2251181059 (7 : ZMod 2251181059)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (53599549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (53599549, 1)] : List FactorBlock).map factorBlockValue).prod) = 2251181059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_53599549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2251181059) ^ 1125590529 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2251181059) ^ 750393686 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2251181059) ^ 321597294 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2251181059) ^ 42 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_2530016107 : Nat.Prime 2530016107 := by
  apply lucas_primality 2530016107 (2 : ZMod 2530016107)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (421669351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (421669351, 1)] : List FactorBlock).map factorBlockValue).prod) = 2530016107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_421669351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2530016107) ^ 1265008053 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2530016107) ^ 843338702 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2530016107) ^ 6 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_2626025873 : Nat.Prime 2626025873 := by
  apply lucas_primality 2626025873 (3 : ZMod 2626025873)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (31, 1), (67, 1), (4159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (31, 1), (67, 1), (4159, 1)] : List FactorBlock).map factorBlockValue).prod) = 2626025873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_19
      · exact prime_seventyFourBT_31
      · exact prime_seventyFourBT_67
      · exact prime_seventyFourBT_4159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2626025873) ^ 1313012936 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2626025873) ^ 138211888 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2626025873) ^ 84710512 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2626025873) ^ 39194416 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2626025873) ^ 631408 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_2799093559 : Nat.Prime 2799093559 := by
  apply lucas_primality 2799093559 (3 : ZMod 2799093559)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (8802181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (8802181, 1)] : List FactorBlock).map factorBlockValue).prod) = 2799093559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_53
      · exact prime_seventyFourBT_8802181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2799093559) ^ 1399546779 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2799093559) ^ 933031186 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2799093559) ^ 52813086 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2799093559) ^ 318 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_3138532723 : Nat.Prime 3138532723 := by
  apply lucas_primality 3138532723 (2 : ZMod 3138532723)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (149, 1), (90017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (149, 1), (90017, 1)] : List FactorBlock).map factorBlockValue).prod) = 3138532723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_149
      · exact prime_seventyFourBT_90017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3138532723) ^ 1569266361 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3138532723) ^ 1046177574 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3138532723) ^ 241425594 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3138532723) ^ 21063978 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3138532723) ^ 34866 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_3583195489 : Nat.Prime 3583195489 := by
  apply lucas_primality 3583195489 (14 : ZMod 3583195489)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (769, 1), (5393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (769, 1), (5393, 1)] : List FactorBlock).map factorBlockValue).prod) = 3583195489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_769
      · exact prime_seventyFourBT_5393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 3583195489) ^ 1791597744 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 3583195489) ^ 1194398496 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 3583195489) ^ 4659552 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 3583195489) ^ 664416 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_3664558397 : Nat.Prime 3664558397 := by
  apply lucas_primality 3664558397 (2 : ZMod 3664558397)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6967, 1), (131497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6967, 1), (131497, 1)] : List FactorBlock).map factorBlockValue).prod) = 3664558397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_6967
      · exact prime_seventyFourBT_131497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3664558397) ^ 1832279198 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3664558397) ^ 525988 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3664558397) ^ 27868 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_3829246411 : Nat.Prime 3829246411 := by
  apply lucas_primality 3829246411 (3 : ZMod 3829246411)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (1489, 1), (7793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (1489, 1), (7793, 1)] : List FactorBlock).map factorBlockValue).prod) = 3829246411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_1489
      · exact prime_seventyFourBT_7793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3829246411) ^ 1914623205 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3829246411) ^ 1276415470 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3829246411) ^ 765849282 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3829246411) ^ 348113310 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3829246411) ^ 2571690 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3829246411) ^ 491370 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_4071647521 : Nat.Prime 4071647521 := by
  apply lucas_primality 4071647521 (11 : ZMod 4071647521)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (61, 1), (15451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (61, 1), (15451, 1)] : List FactorBlock).map factorBlockValue).prod) = 4071647521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_61
      · exact prime_seventyFourBT_15451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4071647521) ^ 2035823760 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 4071647521) ^ 1357215840 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 4071647521) ^ 814329504 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 4071647521) ^ 66748320 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 4071647521) ^ 263520 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_4242338953 : Nat.Prime 4242338953 := by
  apply lucas_primality 4242338953 (5 : ZMod 4242338953)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (673, 1), (262651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (673, 1), (262651, 1)] : List FactorBlock).map factorBlockValue).prod) = 4242338953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_673
      · exact prime_seventyFourBT_262651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4242338953) ^ 2121169476 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 4242338953) ^ 1414112984 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 4242338953) ^ 6303624 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 4242338953) ^ 16152 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_4310914051 : Nat.Prime 4310914051 := by
  apply lucas_primality 4310914051 (11 : ZMod 4310914051)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (9579809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (9579809, 1)] : List FactorBlock).map factorBlockValue).prod) = 4310914051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_9579809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 4310914051) ^ 2155457025 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 4310914051) ^ 1436971350 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 4310914051) ^ 862182810 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 4310914051) ^ 450 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_4416216319 : Nat.Prime 4416216319 := by
  apply lucas_primality 4416216319 (3 : ZMod 4416216319)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (245345351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (245345351, 1)] : List FactorBlock).map factorBlockValue).prod) = 4416216319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_245345351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4416216319) ^ 2208108159 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4416216319) ^ 1472072106 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4416216319) ^ 18 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_4695503959 : Nat.Prime 4695503959 := by
  apply lucas_primality 4695503959 (3 : ZMod 4695503959)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (23, 1), (3780599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (23, 1), (3780599, 1)] : List FactorBlock).map factorBlockValue).prod) = 4695503959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_23
      · exact prime_seventyFourBT_3780599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4695503959) ^ 2347751979 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4695503959) ^ 1565167986 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4695503959) ^ 204152346 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4695503959) ^ 1242 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_5127750553 : Nat.Prime 5127750553 := by
  apply lucas_primality 5127750553 (5 : ZMod 5127750553)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (1559, 1), (7213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (1559, 1), (7213, 1)] : List FactorBlock).map factorBlockValue).prod) = 5127750553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_19
      · exact prime_seventyFourBT_1559
      · exact prime_seventyFourBT_7213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5127750553) ^ 2563875276 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 5127750553) ^ 1709250184 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 5127750553) ^ 269881608 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 5127750553) ^ 3289128 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 5127750553) ^ 710904 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_5131542343 : Nat.Prime 5131542343 := by
  apply lucas_primality 5131542343 (5 : ZMod 5131542343)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (937, 1), (21227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (937, 1), (21227, 1)] : List FactorBlock).map factorBlockValue).prod) = 5131542343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_43
      · exact prime_seventyFourBT_937
      · exact prime_seventyFourBT_21227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5131542343) ^ 2565771171 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 5131542343) ^ 1710514114 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 5131542343) ^ 119338194 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 5131542343) ^ 5476566 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 5131542343) ^ 241746 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_5195230967 : Nat.Prime 5195230967 := by
  apply lucas_primality 5195230967 (5 : ZMod 5195230967)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (313, 1), (8299091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (313, 1), (8299091, 1)] : List FactorBlock).map factorBlockValue).prod) = 5195230967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_313
      · exact prime_seventyFourBT_8299091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5195230967) ^ 2597615483 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 5195230967) ^ 16598182 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 5195230967) ^ 626 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_5252051747 : Nat.Prime 5252051747 := by
  apply lucas_primality 5252051747 (2 : ZMod 5252051747)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2626025873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2626025873, 1)] : List FactorBlock).map factorBlockValue).prod) = 5252051747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_2626025873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5252051747) ^ 2626025873 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5252051747) ^ 2 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_5462501801 : Nat.Prime 5462501801 := by
  apply lucas_primality 5462501801 (3 : ZMod 5462501801)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (7, 1), (3901787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (7, 1), (3901787, 1)] : List FactorBlock).map factorBlockValue).prod) = 5462501801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_3901787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5462501801) ^ 2731250900 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 5462501801) ^ 1092500360 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 5462501801) ^ 780357400 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 5462501801) ^ 1400 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_5880305411 : Nat.Prime 5880305411 := by
  apply lucas_primality 5880305411 (2 : ZMod 5880305411)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (84004363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (84004363, 1)] : List FactorBlock).map factorBlockValue).prod) = 5880305411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_84004363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5880305411) ^ 2940152705 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5880305411) ^ 1176061082 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5880305411) ^ 840043630 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5880305411) ^ 70 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_6091357949 : Nat.Prime 6091357949 := by
  apply lucas_primality 6091357949 (2 : ZMod 6091357949)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (117141499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (117141499, 1)] : List FactorBlock).map factorBlockValue).prod) = 6091357949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_117141499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6091357949) ^ 3045678974 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6091357949) ^ 468565996 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6091357949) ^ 52 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_6446075173 : Nat.Prime 6446075173 := by
  apply lucas_primality 6446075173 (2 : ZMod 6446075173)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (537172931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (537172931, 1)] : List FactorBlock).map factorBlockValue).prod) = 6446075173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_537172931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6446075173) ^ 3223037586 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6446075173) ^ 2148691724 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6446075173) ^ 12 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_6463806757 : Nat.Prime 6463806757 := by
  apply lucas_primality 6463806757 (2 : ZMod 6463806757)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (263, 1), (186191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (263, 1), (186191, 1)] : List FactorBlock).map factorBlockValue).prod) = 6463806757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_263
      · exact prime_seventyFourBT_186191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6463806757) ^ 3231903378 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6463806757) ^ 2154602252 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6463806757) ^ 587618796 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6463806757) ^ 24577212 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6463806757) ^ 34716 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_7022874739 : Nat.Prime 7022874739 := by
  apply lucas_primality 7022874739 (3 : ZMod 7022874739)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (106407193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (106407193, 1)] : List FactorBlock).map factorBlockValue).prod) = 7022874739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_106407193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7022874739) ^ 3511437369 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 7022874739) ^ 2340958246 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 7022874739) ^ 638443158 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 7022874739) ^ 66 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_7059682523 : Nat.Prime 7059682523 := by
  apply lucas_primality 7059682523 (2 : ZMod 7059682523)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (185781119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (185781119, 1)] : List FactorBlock).map factorBlockValue).prod) = 7059682523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_19
      · exact prime_seventyFourBT_185781119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7059682523) ^ 3529841261 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 7059682523) ^ 371562238 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 7059682523) ^ 38 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_7151778343 : Nat.Prime 7151778343 := by
  apply lucas_primality 7151778343 (3 : ZMod 7151778343)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (7496623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (7496623, 1)] : List FactorBlock).map factorBlockValue).prod) = 7151778343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_53
      · exact prime_seventyFourBT_7496623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7151778343) ^ 3575889171 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 7151778343) ^ 2383926114 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 7151778343) ^ 134939214 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 7151778343) ^ 954 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_10209856973 : Nat.Prime 10209856973 := by
  apply lucas_primality 10209856973 (11 : ZMod 10209856973)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (2351, 1), (22157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (2351, 1), (22157, 1)] : List FactorBlock).map factorBlockValue).prod) = 10209856973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_2351
      · exact prime_seventyFourBT_22157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 10209856973) ^ 5104928486 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 10209856973) ^ 1458550996 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 10209856973) ^ 4342772 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 10209856973) ^ 460796 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_10272879269 : Nat.Prime 10272879269 := by
  apply lucas_primality 10272879269 (2 : ZMod 10272879269)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (22727609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (22727609, 1)] : List FactorBlock).map factorBlockValue).prod) = 10272879269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_113
      · exact prime_seventyFourBT_22727609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10272879269) ^ 5136439634 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10272879269) ^ 90910436 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10272879269) ^ 452 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_10866543899 : Nat.Prime 10866543899 := by
  apply lucas_primality 10866543899 (2 : ZMod 10866543899)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (3583, 1), (4421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (3583, 1), (4421, 1)] : List FactorBlock).map factorBlockValue).prod) = 10866543899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_3583
      · exact prime_seventyFourBT_4421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10866543899) ^ 5433271949 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10866543899) ^ 1552363414 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10866543899) ^ 3032806 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10866543899) ^ 2457938 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_11910173269 : Nat.Prime 11910173269 := by
  apply lucas_primality 11910173269 (2 : ZMod 11910173269)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (389, 2), (937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (389, 2), (937, 1)] : List FactorBlock).map factorBlockValue).prod) = 11910173269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_389
      · exact prime_seventyFourBT_937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11910173269) ^ 5955086634 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 11910173269) ^ 3970057756 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 11910173269) ^ 1701453324 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 11910173269) ^ 30617412 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 11910173269) ^ 12710964 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_12380482967 : Nat.Prime 12380482967 := by
  apply lucas_primality 12380482967 (5 : ZMod 12380482967)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (641, 1), (9657163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (641, 1), (9657163, 1)] : List FactorBlock).map factorBlockValue).prod) = 12380482967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_641
      · exact prime_seventyFourBT_9657163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 12380482967) ^ 6190241483 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 12380482967) ^ 19314326 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 12380482967) ^ 1282 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_14015824021 : Nat.Prime 14015824021 := by
  apply lucas_primality 14015824021 (10 : ZMod 14015824021)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (11, 1), (7078699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (11, 1), (7078699, 1)] : List FactorBlock).map factorBlockValue).prod) = 14015824021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_7078699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 14015824021) ^ 7007912010 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 14015824021) ^ 4671941340 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 14015824021) ^ 2803164804 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 14015824021) ^ 1274165820 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 14015824021) ^ 1980 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_15229531001 : Nat.Prime 15229531001 := by
  apply lucas_primality 15229531001 (6 : ZMod 15229531001)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (15229531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (15229531, 1)] : List FactorBlock).map factorBlockValue).prod) = 15229531001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_15229531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 15229531001) ^ 7614765500 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 15229531001) ^ 3045906200 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 15229531001) ^ 1000 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_16349153731 : Nat.Prime 16349153731 := by
  apply lucas_primality 16349153731 (3 : ZMod 16349153731)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (73, 1), (82037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (73, 1), (82037, 1)] : List FactorBlock).map factorBlockValue).prod) = 16349153731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_73
      · exact prime_seventyFourBT_82037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16349153731) ^ 8174576865 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 16349153731) ^ 5449717910 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 16349153731) ^ 3269830746 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 16349153731) ^ 2335593390 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 16349153731) ^ 1257627210 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 16349153731) ^ 223961010 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 16349153731) ^ 199290 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_17330887369 : Nat.Prime 17330887369 := by
  apply lucas_primality 17330887369 (7 : ZMod 17330887369)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (73, 1), (3297353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (73, 1), (3297353, 1)] : List FactorBlock).map factorBlockValue).prod) = 17330887369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_73
      · exact prime_seventyFourBT_3297353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 17330887369) ^ 8665443684 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 17330887369) ^ 5776962456 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 17330887369) ^ 237409416 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 17330887369) ^ 5256 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_17749788803 : Nat.Prime 17749788803 := by
  apply lucas_primality 17749788803 (2 : ZMod 17749788803)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (1093, 1), (137623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (1093, 1), (137623, 1)] : List FactorBlock).map factorBlockValue).prod) = 17749788803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_59
      · exact prime_seventyFourBT_1093
      · exact prime_seventyFourBT_137623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17749788803) ^ 8874894401 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 17749788803) ^ 300843878 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 17749788803) ^ 16239514 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 17749788803) ^ 128974 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_20419713947 : Nat.Prime 20419713947 := by
  apply lucas_primality 20419713947 (2 : ZMod 20419713947)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10209856973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10209856973, 1)] : List FactorBlock).map factorBlockValue).prod) = 20419713947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_10209856973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 20419713947) ^ 10209856973 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 20419713947) ^ 2 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_20434021631 : Nat.Prime 20434021631 := by
  apply lucas_primality 20434021631 (7 : ZMod 20434021631)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (185763833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (185763833, 1)] : List FactorBlock).map factorBlockValue).prod) = 20434021631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_185763833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 20434021631) ^ 10217010815 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 20434021631) ^ 4086804326 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 20434021631) ^ 1857638330 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 20434021631) ^ 110 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_21017099591 : Nat.Prime 21017099591 := by
  apply lucas_primality 21017099591 (11 : ZMod 21017099591)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (151, 1), (13918609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (151, 1), (13918609, 1)] : List FactorBlock).map factorBlockValue).prod) = 21017099591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_151
      · exact prime_seventyFourBT_13918609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 21017099591) ^ 10508549795 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 21017099591) ^ 4203419918 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 21017099591) ^ 139186090 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 21017099591) ^ 1510 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_23124067081 : Nat.Prime 23124067081 := by
  apply lucas_primality 23124067081 (14 : ZMod 23124067081)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17, 1), (11335327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17, 1), (11335327, 1)] : List FactorBlock).map factorBlockValue).prod) = 23124067081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_17
      · exact prime_seventyFourBT_11335327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 23124067081) ^ 11562033540 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 23124067081) ^ 7708022360 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 23124067081) ^ 4624813416 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 23124067081) ^ 1360239240 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 23124067081) ^ 2040 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_28091498957 : Nat.Prime 28091498957 := by
  apply lucas_primality 28091498957 (2 : ZMod 28091498957)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7022874739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7022874739, 1)] : List FactorBlock).map factorBlockValue).prod) = 28091498957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_7022874739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 28091498957) ^ 14045749478 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28091498957) ^ 4 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_28876649411 : Nat.Prime 28876649411 := by
  apply lucas_primality 28876649411 (2 : ZMod 28876649411)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (113, 1), (3650651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (113, 1), (3650651, 1)] : List FactorBlock).map factorBlockValue).prod) = 28876649411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_113
      · exact prime_seventyFourBT_3650651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28876649411) ^ 14438324705 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28876649411) ^ 5775329882 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28876649411) ^ 4125235630 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28876649411) ^ 255545570 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28876649411) ^ 7910 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_29673934067 : Nat.Prime 29673934067 := by
  apply lucas_primality 29673934067 (2 : ZMod 29673934067)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (57285587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (57285587, 1)] : List FactorBlock).map factorBlockValue).prod) = 29673934067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_37
      · exact prime_seventyFourBT_57285587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 29673934067) ^ 14836967033 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 29673934067) ^ 4239133438 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 29673934067) ^ 801998218 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 29673934067) ^ 518 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_29733866951 : Nat.Prime 29733866951 := by
  apply lucas_primality 29733866951 (19 : ZMod 29733866951)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (594677339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (594677339, 1)] : List FactorBlock).map factorBlockValue).prod) = 29733866951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_594677339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 29733866951) ^ 14866933475 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (19 : ZMod 29733866951) ^ 5946773390 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (19 : ZMod 29733866951) ^ 50 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_30123538369 : Nat.Prime 30123538369 := by
  apply lucas_primality 30123538369 (13 : ZMod 30123538369)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (11, 1), (41, 1), (49697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (11, 1), (41, 1), (49697, 1)] : List FactorBlock).map factorBlockValue).prod) = 30123538369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_41
      · exact prime_seventyFourBT_49697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 30123538369) ^ 15061769184 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 30123538369) ^ 10041179456 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 30123538369) ^ 4303362624 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 30123538369) ^ 2738503488 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 30123538369) ^ 734720448 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 30123538369) ^ 606144 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_33434089751 : Nat.Prime 33434089751 := by
  apply lucas_primality 33434089751 (17 : ZMod 33434089751)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (653, 1), (204803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (653, 1), (204803, 1)] : List FactorBlock).map factorBlockValue).prod) = 33434089751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_653
      · exact prime_seventyFourBT_204803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 33434089751) ^ 16717044875 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (17 : ZMod 33434089751) ^ 6686817950 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (17 : ZMod 33434089751) ^ 51200750 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (17 : ZMod 33434089751) ^ 163250 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_41921029019 : Nat.Prime 41921029019 := by
  apply lucas_primality 41921029019 (2 : ZMod 41921029019)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (503, 1), (3788273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (503, 1), (3788273, 1)] : List FactorBlock).map factorBlockValue).prod) = 41921029019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_503
      · exact prime_seventyFourBT_3788273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41921029019) ^ 20960514509 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 41921029019) ^ 3811002638 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 41921029019) ^ 83342006 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 41921029019) ^ 11066 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_42002098639 : Nat.Prime 42002098639 := by
  apply lucas_primality 42002098639 (6 : ZMod 42002098639)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5167, 1), (1354819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5167, 1), (1354819, 1)] : List FactorBlock).map factorBlockValue).prod) = 42002098639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5167
      · exact prime_seventyFourBT_1354819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 42002098639) ^ 21001049319 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 42002098639) ^ 14000699546 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 42002098639) ^ 8128914 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 42002098639) ^ 31002 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_42034199183 : Nat.Prime 42034199183 := by
  apply lucas_primality 42034199183 (5 : ZMod 42034199183)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (21017099591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (21017099591, 1)] : List FactorBlock).map factorBlockValue).prod) = 42034199183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_21017099591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 42034199183) ^ 21017099591 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 42034199183) ^ 2 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_59467733903 : Nat.Prime 59467733903 := by
  apply lucas_primality 59467733903 (5 : ZMod 59467733903)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29733866951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29733866951, 1)] : List FactorBlock).map factorBlockValue).prod) = 59467733903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_29733866951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 59467733903) ^ 29733866951 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 59467733903) ^ 2 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_61102668379 : Nat.Prime 61102668379 := by
  apply lucas_primality 61102668379 (2 : ZMod 61102668379)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (463, 1), (479, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (463, 1), (479, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) = 61102668379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_47
      · exact prime_seventyFourBT_463
      · exact prime_seventyFourBT_479
      · exact prime_seventyFourBT_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 61102668379) ^ 30551334189 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 61102668379) ^ 20367556126 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 61102668379) ^ 1300056774 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 61102668379) ^ 131971206 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 61102668379) ^ 127562982 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 61102668379) ^ 62541114 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_61304433943 : Nat.Prime 61304433943 := by
  apply lucas_primality 61304433943 (3 : ZMod 61304433943)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (277, 1), (1271929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (277, 1), (1271929, 1)] : List FactorBlock).map factorBlockValue).prod) = 61304433943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_29
      · exact prime_seventyFourBT_277
      · exact prime_seventyFourBT_1271929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 61304433943) ^ 30652216971 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 61304433943) ^ 20434811314 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 61304433943) ^ 2113945998 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 61304433943) ^ 221315646 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 61304433943) ^ 48198 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_65809442371 : Nat.Prime 65809442371 := by
  apply lucas_primality 65809442371 (22 : ZMod 65809442371)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (1783, 1), (175759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1783, 1), (175759, 1)] : List FactorBlock).map factorBlockValue).prod) = 65809442371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_1783
      · exact prime_seventyFourBT_175759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 65809442371) ^ 32904721185 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (22 : ZMod 65809442371) ^ 21936480790 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (22 : ZMod 65809442371) ^ 13161888474 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (22 : ZMod 65809442371) ^ 9401348910 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (22 : ZMod 65809442371) ^ 36909390 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (22 : ZMod 65809442371) ^ 374430 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_68720903213 : Nat.Prime 68720903213 := by
  apply lucas_primality 68720903213 (2 : ZMod 68720903213)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (1321555831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (1321555831, 1)] : List FactorBlock).map factorBlockValue).prod) = 68720903213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_1321555831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 68720903213) ^ 34360451606 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 68720903213) ^ 5286223324 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 68720903213) ^ 52 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_73683900221 : Nat.Prime 73683900221 := by
  apply lucas_primality 73683900221 (3 : ZMod 73683900221)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (277, 1), (1900049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (277, 1), (1900049, 1)] : List FactorBlock).map factorBlockValue).prod) = 73683900221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_277
      · exact prime_seventyFourBT_1900049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 73683900221) ^ 36841950110 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 73683900221) ^ 14736780044 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 73683900221) ^ 10526271460 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 73683900221) ^ 266006860 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 73683900221) ^ 38780 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_80004182849 : Nat.Prime 80004182849 := by
  apply lucas_primality 80004182849 (3 : ZMod 80004182849)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (14797, 1), (84481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (14797, 1), (84481, 1)] : List FactorBlock).map factorBlockValue).prod) = 80004182849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_14797
      · exact prime_seventyFourBT_84481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 80004182849) ^ 40002091424 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 80004182849) ^ 5406784 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 80004182849) ^ 947008 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_95169181007 : Nat.Prime 95169181007 := by
  apply lucas_primality 95169181007 (5 : ZMod 95169181007)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (2799093559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (2799093559, 1)] : List FactorBlock).map factorBlockValue).prod) = 95169181007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_17
      · exact prime_seventyFourBT_2799093559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 95169181007) ^ 47584590503 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 95169181007) ^ 5598187118 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 95169181007) ^ 34 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_108270938051 : Nat.Prime 108270938051 := by
  apply lucas_primality 108270938051 (2 : ZMod 108270938051)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (67, 1), (191, 1), (15383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (67, 1), (191, 1), (15383, 1)] : List FactorBlock).map factorBlockValue).prod) = 108270938051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_67
      · exact prime_seventyFourBT_191
      · exact prime_seventyFourBT_15383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 108270938051) ^ 54135469025 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 108270938051) ^ 21654187610 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 108270938051) ^ 9842812550 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 108270938051) ^ 1615984150 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 108270938051) ^ 566863550 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 108270938051) ^ 7038350 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_141193650461 : Nat.Prime 141193650461 := by
  apply lucas_primality 141193650461 (2 : ZMod 141193650461)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7059682523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7059682523, 1)] : List FactorBlock).map factorBlockValue).prod) = 141193650461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7059682523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 141193650461) ^ 70596825230 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 141193650461) ^ 28238730092 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 141193650461) ^ 20 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_144117741709 : Nat.Prime 144117741709 := by
  apply lucas_primality 144117741709 (6 : ZMod 144117741709)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (71, 1), (56384093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (71, 1), (56384093, 1)] : List FactorBlock).map factorBlockValue).prod) = 144117741709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_71
      · exact prime_seventyFourBT_56384093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 144117741709) ^ 72058870854 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 144117741709) ^ 48039247236 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 144117741709) ^ 2029827348 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 144117741709) ^ 2556 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_147367800443 : Nat.Prime 147367800443 := by
  apply lucas_primality 147367800443 (2 : ZMod 147367800443)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73683900221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73683900221, 1)] : List FactorBlock).map factorBlockValue).prod) = 147367800443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_73683900221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 147367800443) ^ 73683900221 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 147367800443) ^ 2 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_156424976273 : Nat.Prime 156424976273 := by
  apply lucas_primality 156424976273 (3 : ZMod 156424976273)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (269, 1), (1912847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (269, 1), (1912847, 1)] : List FactorBlock).map factorBlockValue).prod) = 156424976273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_19
      · exact prime_seventyFourBT_269
      · exact prime_seventyFourBT_1912847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 156424976273) ^ 78212488136 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 156424976273) ^ 8232893488 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 156424976273) ^ 581505488 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 156424976273) ^ 81776 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_240134849173 : Nat.Prime 240134849173 := by
  apply lucas_primality 240134849173 (2 : ZMod 240134849173)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (9281, 1), (718717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (9281, 1), (718717, 1)] : List FactorBlock).map factorBlockValue).prod) = 240134849173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_9281
      · exact prime_seventyFourBT_718717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 240134849173) ^ 120067424586 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 240134849173) ^ 80044949724 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 240134849173) ^ 25873812 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 240134849173) ^ 334116 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_244410673517 : Nat.Prime 244410673517 := by
  apply lucas_primality 244410673517 (2 : ZMod 244410673517)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61102668379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61102668379, 1)] : List FactorBlock).map factorBlockValue).prod) = 244410673517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_61102668379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 244410673517) ^ 122205336758 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 244410673517) ^ 4 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_294920504287 : Nat.Prime 294920504287 := by
  apply lucas_primality 294920504287 (3 : ZMod 294920504287)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 2), (170081029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 2), (170081029, 1)] : List FactorBlock).map factorBlockValue).prod) = 294920504287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_17
      · exact prime_seventyFourBT_170081029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 294920504287) ^ 147460252143 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 294920504287) ^ 98306834762 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 294920504287) ^ 17348264958 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 294920504287) ^ 1734 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_295262222851 : Nat.Prime 295262222851 := by
  apply lucas_primality 295262222851 (3 : ZMod 295262222851)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (7, 2), (17, 1), (23, 2), (1489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (7, 2), (17, 1), (23, 2), (1489, 1)] : List FactorBlock).map factorBlockValue).prod) = 295262222851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_17
      · exact prime_seventyFourBT_23
      · exact prime_seventyFourBT_1489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 295262222851) ^ 147631111425 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 295262222851) ^ 98420740950 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 295262222851) ^ 59052444570 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 295262222851) ^ 42180317550 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 295262222851) ^ 17368366050 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 295262222851) ^ 12837487950 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 295262222851) ^ 198295650 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_341098439287 : Nat.Prime 341098439287 := by
  apply lucas_primality 341098439287 (3 : ZMod 341098439287)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 3), (2221, 1), (19231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 3), (2221, 1), (19231, 1)] : List FactorBlock).map factorBlockValue).prod) = 341098439287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_2221
      · exact prime_seventyFourBT_19231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 341098439287) ^ 170549219643 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 341098439287) ^ 113699479762 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 341098439287) ^ 31008949026 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 341098439287) ^ 153578766 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 341098439287) ^ 17736906 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_348088059343 : Nat.Prime 348088059343 := by
  apply lucas_primality 348088059343 (5 : ZMod 348088059343)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (6446075173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (6446075173, 1)] : List FactorBlock).map factorBlockValue).prod) = 348088059343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_6446075173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 348088059343) ^ 174044029671 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 348088059343) ^ 116029353114 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 348088059343) ^ 54 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_354445348729 : Nat.Prime 354445348729 := by
  apply lucas_primality 354445348729 (7 : ZMod 354445348729)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (73, 1), (521, 1), (16883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (73, 1), (521, 1), (16883, 1)] : List FactorBlock).map factorBlockValue).prod) = 354445348729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_23
      · exact prime_seventyFourBT_73
      · exact prime_seventyFourBT_521
      · exact prime_seventyFourBT_16883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 354445348729) ^ 177222674364 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 354445348729) ^ 118148449576 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 354445348729) ^ 15410667336 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 354445348729) ^ 4855415736 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 354445348729) ^ 680317368 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 354445348729) ^ 20994216 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_367826603659 : Nat.Prime 367826603659 := by
  apply lucas_primality 367826603659 (2 : ZMod 367826603659)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61304433943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61304433943, 1)] : List FactorBlock).map factorBlockValue).prod) = 367826603659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_61304433943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 367826603659) ^ 183913301829 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 367826603659) ^ 122608867886 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 367826603659) ^ 6 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_390454707857 : Nat.Prime 390454707857 := by
  apply lucas_primality 390454707857 (3 : ZMod 390454707857)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (241, 1), (4289, 1), (23609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (241, 1), (4289, 1), (23609, 1)] : List FactorBlock).map factorBlockValue).prod) = 390454707857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_241
      · exact prime_seventyFourBT_4289
      · exact prime_seventyFourBT_23609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 390454707857) ^ 195227353928 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 390454707857) ^ 1620144016 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 390454707857) ^ 91036304 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 390454707857) ^ 16538384 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_493624249913 : Nat.Prime 493624249913 := by
  apply lucas_primality 493624249913 (3 : ZMod 493624249913)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (14771, 1), (4177309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (14771, 1), (4177309, 1)] : List FactorBlock).map factorBlockValue).prod) = 493624249913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_14771
      · exact prime_seventyFourBT_4177309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 493624249913) ^ 246812124956 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 493624249913) ^ 33418472 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 493624249913) ^ 118168 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_502874374831 : Nat.Prime 502874374831 := by
  apply lucas_primality 502874374831 (3 : ZMod 502874374831)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (191, 1), (331, 1), (265141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (191, 1), (331, 1), (265141, 1)] : List FactorBlock).map factorBlockValue).prod) = 502874374831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_191
      · exact prime_seventyFourBT_331
      · exact prime_seventyFourBT_265141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 502874374831) ^ 251437187415 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 502874374831) ^ 167624791610 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 502874374831) ^ 100574874966 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 502874374831) ^ 2632850130 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 502874374831) ^ 1519257930 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 502874374831) ^ 1896630 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_604206691069 : Nat.Prime 604206691069 := by
  apply lucas_primality 604206691069 (2 : ZMod 604206691069)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (109, 1), (311, 1), (673, 1), (2207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (109, 1), (311, 1), (673, 1), (2207, 1)] : List FactorBlock).map factorBlockValue).prod) = 604206691069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_109
      · exact prime_seventyFourBT_311
      · exact prime_seventyFourBT_673
      · exact prime_seventyFourBT_2207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 604206691069) ^ 302103345534 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 604206691069) ^ 201402230356 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 604206691069) ^ 5543180652 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 604206691069) ^ 1942786788 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 604206691069) ^ 897781116 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 604206691069) ^ 273768324 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_722964920857 : Nat.Prime 722964920857 := by
  apply lucas_primality 722964920857 (10 : ZMod 722964920857)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (30123538369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (30123538369, 1)] : List FactorBlock).map factorBlockValue).prod) = 722964920857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_30123538369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 722964920857) ^ 361482460428 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 722964920857) ^ 240988306952 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 722964920857) ^ 24 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_803213020193 : Nat.Prime 803213020193 := by
  apply lucas_primality 803213020193 (3 : ZMod 803213020193)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (307, 1), (7432753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (307, 1), (7432753, 1)] : List FactorBlock).map factorBlockValue).prod) = 803213020193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_307
      · exact prime_seventyFourBT_7432753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 803213020193) ^ 401606510096 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 803213020193) ^ 73019365472 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 803213020193) ^ 2616329056 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 803213020193) ^ 108064 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_847161902767 : Nat.Prime 847161902767 := by
  apply lucas_primality 847161902767 (5 : ZMod 847161902767)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (141193650461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (141193650461, 1)] : List FactorBlock).map factorBlockValue).prod) = 847161902767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_141193650461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 847161902767) ^ 423580951383 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 847161902767) ^ 282387300922 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 847161902767) ^ 6 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_886364223859 : Nat.Prime 886364223859 := by
  apply lucas_primality 886364223859 (3 : ZMod 886364223859)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (37, 1), (67, 1), (79, 1), (8111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (37, 1), (67, 1), (79, 1), (8111, 1)] : List FactorBlock).map factorBlockValue).prod) = 886364223859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_31
      · exact prime_seventyFourBT_37
      · exact prime_seventyFourBT_67
      · exact prime_seventyFourBT_79
      · exact prime_seventyFourBT_8111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 886364223859) ^ 443182111929 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 886364223859) ^ 295454741286 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 886364223859) ^ 28592394318 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 886364223859) ^ 23955789834 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 886364223859) ^ 13229316774 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 886364223859) ^ 11219800302 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 886364223859) ^ 109279278 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_999722038709 : Nat.Prime 999722038709 := by
  apply lucas_primality 999722038709 (2 : ZMod 999722038709)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (10866543899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (10866543899, 1)] : List FactorBlock).map factorBlockValue).prod) = 999722038709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_23
      · exact prime_seventyFourBT_10866543899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 999722038709) ^ 499861019354 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 999722038709) ^ 43466175596 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 999722038709) ^ 92 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1267295939291 : Nat.Prime 1267295939291 := by
  apply lucas_primality 1267295939291 (2 : ZMod 1267295939291)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (81077, 1), (1563077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (81077, 1), (1563077, 1)] : List FactorBlock).map factorBlockValue).prod) = 1267295939291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_81077
      · exact prime_seventyFourBT_1563077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1267295939291) ^ 633647969645 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1267295939291) ^ 253459187858 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1267295939291) ^ 15630770 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1267295939291) ^ 810770 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1382099294833 : Nat.Prime 1382099294833 := by
  apply lucas_primality 1382099294833 (7 : ZMod 1382099294833)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1039, 1), (27712931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1039, 1), (27712931, 1)] : List FactorBlock).map factorBlockValue).prod) = 1382099294833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_1039
      · exact prime_seventyFourBT_27712931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1382099294833) ^ 691049647416 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 1382099294833) ^ 460699764944 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 1382099294833) ^ 1330220688 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 1382099294833) ^ 49872 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1478249829697 : Nat.Prime 1478249829697 := by
  apply lucas_primality 1478249829697 (5 : ZMod 1478249829697)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (83, 1), (199, 1), (466139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (83, 1), (199, 1), (466139, 1)] : List FactorBlock).map factorBlockValue).prod) = 1478249829697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_83
      · exact prime_seventyFourBT_199
      · exact prime_seventyFourBT_466139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1478249829697) ^ 739124914848 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1478249829697) ^ 492749943232 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1478249829697) ^ 17810238912 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1478249829697) ^ 7428391104 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1478249829697) ^ 3171264 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1509712241407 : Nat.Prime 1509712241407 := by
  apply lucas_primality 1509712241407 (3 : ZMod 1509712241407)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (11927, 1), (204821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (11927, 1), (204821, 1)] : List FactorBlock).map factorBlockValue).prod) = 1509712241407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_103
      · exact prime_seventyFourBT_11927
      · exact prime_seventyFourBT_204821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1509712241407) ^ 754856120703 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1509712241407) ^ 503237413802 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1509712241407) ^ 14657400402 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1509712241407) ^ 126579378 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1509712241407) ^ 7370886 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1521421305143 : Nat.Prime 1521421305143 := by
  apply lucas_primality 1521421305143 (5 : ZMod 1521421305143)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9769, 1), (77869859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9769, 1), (77869859, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521421305143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_9769
      · exact prime_seventyFourBT_77869859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1521421305143) ^ 760710652571 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1521421305143) ^ 155739718 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1521421305143) ^ 19538 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1737061132691 : Nat.Prime 1737061132691 := by
  apply lucas_primality 1737061132691 (6 : ZMod 1737061132691)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (859, 1), (15555307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (859, 1), (15555307, 1)] : List FactorBlock).map factorBlockValue).prod) = 1737061132691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_859
      · exact prime_seventyFourBT_15555307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1737061132691) ^ 868530566345 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1737061132691) ^ 347412226538 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1737061132691) ^ 133620087130 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1737061132691) ^ 2022189910 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1737061132691) ^ 111670 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_2312649612193 : Nat.Prime 2312649612193 := by
  apply lucas_primality 2312649612193 (10 : ZMod 2312649612193)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (59879, 1), (402313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (59879, 1), (402313, 1)] : List FactorBlock).map factorBlockValue).prod) = 2312649612193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_59879
      · exact prime_seventyFourBT_402313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2312649612193) ^ 1156324806096 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2312649612193) ^ 770883204064 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2312649612193) ^ 38622048 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2312649612193) ^ 5748384 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_2547176876197 : Nat.Prime 2547176876197 := by
  apply lucas_primality 2547176876197 (5 : ZMod 2547176876197)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (12541, 1), (16925663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (12541, 1), (16925663, 1)] : List FactorBlock).map factorBlockValue).prod) = 2547176876197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_12541
      · exact prime_seventyFourBT_16925663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2547176876197) ^ 1273588438098 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2547176876197) ^ 849058958732 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2547176876197) ^ 203107956 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2547176876197) ^ 150492 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_2832104223829 : Nat.Prime 2832104223829 := by
  apply lucas_primality 2832104223829 (7 : ZMod 2832104223829)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (7151778343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (7151778343, 1)] : List FactorBlock).map factorBlockValue).prod) = 2832104223829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_7151778343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2832104223829) ^ 1416052111914 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2832104223829) ^ 944034741276 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2832104223829) ^ 257464020348 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2832104223829) ^ 396 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_2934244846207 : Nat.Prime 2934244846207 := by
  apply lucas_primality 2934244846207 (3 : ZMod 2934244846207)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (13177, 1), (651109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (13177, 1), (651109, 1)] : List FactorBlock).map factorBlockValue).prod) = 2934244846207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_19
      · exact prime_seventyFourBT_13177
      · exact prime_seventyFourBT_651109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2934244846207) ^ 1467122423103 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2934244846207) ^ 978081615402 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2934244846207) ^ 154433939274 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2934244846207) ^ 222679278 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2934244846207) ^ 4506534 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_3718941121061 : Nat.Prime 3718941121061 := by
  apply lucas_primality 3718941121061 (2 : ZMod 3718941121061)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (23, 1), (10663, 1), (68927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (23, 1), (10663, 1), (68927, 1)] : List FactorBlock).map factorBlockValue).prod) = 3718941121061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_23
      · exact prime_seventyFourBT_10663
      · exact prime_seventyFourBT_68927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3718941121061) ^ 1859470560530 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3718941121061) ^ 743788224212 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3718941121061) ^ 338085556460 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3718941121061) ^ 161693092220 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3718941121061) ^ 348770620 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3718941121061) ^ 53954780 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_4260751404781 : Nat.Prime 4260751404781 := by
  apply lucas_primality 4260751404781 (10 : ZMod 4260751404781)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (5462501801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (5462501801, 1)] : List FactorBlock).map factorBlockValue).prod) = 4260751404781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_5462501801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 4260751404781) ^ 2130375702390 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 4260751404781) ^ 1420250468260 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 4260751404781) ^ 852150280956 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 4260751404781) ^ 327750108060 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 4260751404781) ^ 780 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_4327885505539 : Nat.Prime 4327885505539 := by
  apply lucas_primality 4327885505539 (7 : ZMod 4327885505539)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (1283, 1), (26771861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (1283, 1), (26771861, 1)] : List FactorBlock).map factorBlockValue).prod) = 4327885505539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_1283
      · exact prime_seventyFourBT_26771861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4327885505539) ^ 2163942752769 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 4327885505539) ^ 1442628501846 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 4327885505539) ^ 618269357934 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 4327885505539) ^ 3373254486 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 4327885505539) ^ 161658 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_4755684304529 : Nat.Prime 4755684304529 := by
  apply lucas_primality 4755684304529 (3 : ZMod 4755684304529)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (73, 1), (4071647521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (73, 1), (4071647521, 1)] : List FactorBlock).map factorBlockValue).prod) = 4755684304529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_73
      · exact prime_seventyFourBT_4071647521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4755684304529) ^ 2377842152264 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4755684304529) ^ 65146360336 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4755684304529) ^ 1168 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_7227143649337 : Nat.Prime 7227143649337 := by
  apply lucas_primality 7227143649337 (7 : ZMod 7227143649337)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (19, 1), (193, 1), (317, 1), (19927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (19, 1), (193, 1), (317, 1), (19927, 1)] : List FactorBlock).map factorBlockValue).prod) = 7227143649337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_19
      · exact prime_seventyFourBT_193
      · exact prime_seventyFourBT_317
      · exact prime_seventyFourBT_19927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7227143649337) ^ 3613571824668 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 7227143649337) ^ 2409047883112 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 7227143649337) ^ 555934126872 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 7227143649337) ^ 380375981544 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 7227143649337) ^ 37446340152 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 7227143649337) ^ 22798560408 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 7227143649337) ^ 362680968 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_8543086601051 : Nat.Prime 8543086601051 := by
  apply lucas_primality 8543086601051 (2 : ZMod 8543086601051)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (661, 1), (258489761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (661, 1), (258489761, 1)] : List FactorBlock).map factorBlockValue).prod) = 8543086601051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_661
      · exact prime_seventyFourBT_258489761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8543086601051) ^ 4271543300525 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8543086601051) ^ 1708617320210 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8543086601051) ^ 12924488050 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8543086601051) ^ 33050 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_9101645662069 : Nat.Prime 9101645662069 := by
  apply lucas_primality 9101645662069 (2 : ZMod 9101645662069)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (28091498957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (28091498957, 1)] : List FactorBlock).map factorBlockValue).prod) = 9101645662069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_28091498957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9101645662069) ^ 4550822831034 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 9101645662069) ^ 3033881887356 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 9101645662069) ^ 324 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_10636370686309 : Nat.Prime 10636370686309 := by
  apply lucas_primality 10636370686309 (2 : ZMod 10636370686309)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (886364223859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (886364223859, 1)] : List FactorBlock).map factorBlockValue).prod) = 10636370686309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_886364223859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10636370686309) ^ 5318185343154 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10636370686309) ^ 3545456895436 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10636370686309) ^ 12 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_16189238304919 : Nat.Prime 16189238304919 := by
  apply lucas_primality 16189238304919 (3 : ZMod 16189238304919)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (37, 1), (313, 1), (11094553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (37, 1), (313, 1), (11094553, 1)] : List FactorBlock).map factorBlockValue).prod) = 16189238304919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_37
      · exact prime_seventyFourBT_313
      · exact prime_seventyFourBT_11094553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16189238304919) ^ 8094619152459 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 16189238304919) ^ 5396412768306 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 16189238304919) ^ 2312748329274 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 16189238304919) ^ 437546981214 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 16189238304919) ^ 51722806086 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 16189238304919) ^ 1459206 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_17528132113733 : Nat.Prime 17528132113733 := by
  apply lucas_primality 17528132113733 (2 : ZMod 17528132113733)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (53, 1), (389, 1), (6856279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (53, 1), (389, 1), (6856279, 1)] : List FactorBlock).map factorBlockValue).prod) = 17528132113733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_31
      · exact prime_seventyFourBT_53
      · exact prime_seventyFourBT_389
      · exact prime_seventyFourBT_6856279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17528132113733) ^ 8764066056866 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 17528132113733) ^ 565423616572 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 17528132113733) ^ 330719473844 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 17528132113733) ^ 45059465588 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 17528132113733) ^ 2556508 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_30712054193467 : Nat.Prime 30712054193467 := by
  apply lucas_primality 30712054193467 (2 : ZMod 30712054193467)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41597, 1), (123053963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41597, 1), (123053963, 1)] : List FactorBlock).map factorBlockValue).prod) = 30712054193467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_41597
      · exact prime_seventyFourBT_123053963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30712054193467) ^ 15356027096733 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 30712054193467) ^ 10237351397822 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 30712054193467) ^ 738323778 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 30712054193467) ^ 249582 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_31428976639783 : Nat.Prime 31428976639783 := by
  apply lucas_primality 31428976639783 (3 : ZMod 31428976639783)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (83, 1), (1297, 1), (1569637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (83, 1), (1297, 1), (1569637, 1)] : List FactorBlock).map factorBlockValue).prod) = 31428976639783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_31
      · exact prime_seventyFourBT_83
      · exact prime_seventyFourBT_1297
      · exact prime_seventyFourBT_1569637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 31428976639783) ^ 15714488319891 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 31428976639783) ^ 10476325546594 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 31428976639783) ^ 1013837956122 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 31428976639783) ^ 378662369154 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 31428976639783) ^ 24232056006 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 31428976639783) ^ 20023086 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_48131078807381 : Nat.Prime 48131078807381 := by
  apply lucas_primality 48131078807381 (2 : ZMod 48131078807381)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (47, 1), (198833, 1), (257519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (47, 1), (198833, 1), (257519, 1)] : List FactorBlock).map factorBlockValue).prod) = 48131078807381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_47
      · exact prime_seventyFourBT_198833
      · exact prime_seventyFourBT_257519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 48131078807381) ^ 24065539403690 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 48131078807381) ^ 9626215761476 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 48131078807381) ^ 1024065506540 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 48131078807381) ^ 242067860 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 48131078807381) ^ 186903020 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_68344692808409 : Nat.Prime 68344692808409 := by
  apply lucas_primality 68344692808409 (3 : ZMod 68344692808409)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (8543086601051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (8543086601051, 1)] : List FactorBlock).map factorBlockValue).prod) = 68344692808409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_8543086601051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 68344692808409) ^ 34172346404204 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 68344692808409) ^ 8 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_70647842899727 : Nat.Prime 70647842899727 := by
  apply lucas_primality 70647842899727 (5 : ZMod 70647842899727)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1754653, 1), (20131571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1754653, 1), (20131571, 1)] : List FactorBlock).map factorBlockValue).prod) = 70647842899727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_1754653
      · exact prime_seventyFourBT_20131571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 70647842899727) ^ 35323921449863 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 70647842899727) ^ 40263142 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 70647842899727) ^ 3509306 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_77901939099703 : Nat.Prime 77901939099703 := by
  apply lucas_primality 77901939099703 (3 : ZMod 77901939099703)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4327885505539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4327885505539, 1)] : List FactorBlock).map factorBlockValue).prod) = 77901939099703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_4327885505539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 77901939099703) ^ 38950969549851 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 77901939099703) ^ 25967313033234 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 77901939099703) ^ 18 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_88722211546583 : Nat.Prime 88722211546583 := by
  apply lucas_primality 88722211546583 (5 : ZMod 88722211546583)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6863, 1), (6463806757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6863, 1), (6463806757, 1)] : List FactorBlock).map factorBlockValue).prod) = 88722211546583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_6863
      · exact prime_seventyFourBT_6463806757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 88722211546583) ^ 44361105773291 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 88722211546583) ^ 12927613514 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 88722211546583) ^ 13726 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_94195800954371 : Nat.Prime 94195800954371 := by
  apply lucas_primality 94195800954371 (2 : ZMod 94195800954371)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 1), (263, 1), (8849, 1), (76367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 1), (263, 1), (8849, 1), (76367, 1)] : List FactorBlock).map factorBlockValue).prod) = 94195800954371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_53
      · exact prime_seventyFourBT_263
      · exact prime_seventyFourBT_8849
      · exact prime_seventyFourBT_76367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 94195800954371) ^ 47097900477185 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 94195800954371) ^ 18839160190874 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 94195800954371) ^ 1777279263290 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 94195800954371) ^ 358158938990 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 94195800954371) ^ 10644796130 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 94195800954371) ^ 1233462110 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_96105188167123 : Nat.Prime 96105188167123 := by
  apply lucas_primality 96105188167123 (3 : ZMod 96105188167123)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (73091, 1), (3714323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (73091, 1), (3714323, 1)] : List FactorBlock).map factorBlockValue).prod) = 96105188167123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_59
      · exact prime_seventyFourBT_73091
      · exact prime_seventyFourBT_3714323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 96105188167123) ^ 48052594083561 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 96105188167123) ^ 32035062722374 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 96105188167123) ^ 1628901494358 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 96105188167123) ^ 1314870342 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 96105188167123) ^ 25874214 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_97017966156511 : Nat.Prime 97017966156511 := by
  apply lucas_primality 97017966156511 (12 : ZMod 97017966156511)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 2), (53819, 1), (408769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 2), (53819, 1), (408769, 1)] : List FactorBlock).map factorBlockValue).prod) = 97017966156511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_53819
      · exact prime_seventyFourBT_408769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 97017966156511) ^ 48508983078255 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (12 : ZMod 97017966156511) ^ 32339322052170 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (12 : ZMod 97017966156511) ^ 19403593231302 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (12 : ZMod 97017966156511) ^ 13859709450930 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (12 : ZMod 97017966156511) ^ 1802671290 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (12 : ZMod 97017966156511) ^ 237341790 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_109093905910601 : Nat.Prime 109093905910601 := by
  apply lucas_primality 109093905910601 (3 : ZMod 109093905910601)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (13, 1), (173, 1), (242538697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (13, 1), (173, 1), (242538697, 1)] : List FactorBlock).map factorBlockValue).prod) = 109093905910601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_173
      · exact prime_seventyFourBT_242538697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 109093905910601) ^ 54546952955300 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 109093905910601) ^ 21818781182120 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 109093905910601) ^ 8391838916200 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 109093905910601) ^ 630600612200 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 109093905910601) ^ 449800 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_146472332907457 : Nat.Prime 146472332907457 := by
  apply lucas_primality 146472332907457 (5 : ZMod 146472332907457)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (19, 1), (569, 1), (23521621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (19, 1), (569, 1), (23521621, 1)] : List FactorBlock).map factorBlockValue).prod) = 146472332907457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_19
      · exact prime_seventyFourBT_569
      · exact prime_seventyFourBT_23521621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 146472332907457) ^ 73236166453728 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 146472332907457) ^ 48824110969152 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 146472332907457) ^ 7709070153024 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 146472332907457) ^ 257420620224 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 146472332907457) ^ 6227136 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_160098661169897 : Nat.Prime 160098661169897 := by
  apply lucas_primality 160098661169897 (3 : ZMod 160098661169897)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (22807, 1), (877464491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (22807, 1), (877464491, 1)] : List FactorBlock).map factorBlockValue).prod) = 160098661169897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_22807
      · exact prime_seventyFourBT_877464491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 160098661169897) ^ 80049330584948 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 160098661169897) ^ 7019715928 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 160098661169897) ^ 182456 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_166611093709847 : Nat.Prime 166611093709847 := by
  apply lucas_primality 166611093709847 (5 : ZMod 166611093709847)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (543149, 1), (2289181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (543149, 1), (2289181, 1)] : List FactorBlock).map factorBlockValue).prod) = 166611093709847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_67
      · exact prime_seventyFourBT_543149
      · exact prime_seventyFourBT_2289181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 166611093709847) ^ 83305546854923 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 166611093709847) ^ 2486732741938 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 166611093709847) ^ 306750254 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 166611093709847) ^ 72781966 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_178099148585257 : Nat.Prime 178099148585257 := by
  apply lucas_primality 178099148585257 (5 : ZMod 178099148585257)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (109, 1), (3583195489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (109, 1), (3583195489, 1)] : List FactorBlock).map factorBlockValue).prod) = 178099148585257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_19
      · exact prime_seventyFourBT_109
      · exact prime_seventyFourBT_3583195489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 178099148585257) ^ 89049574292628 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 178099148585257) ^ 59366382861752 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 178099148585257) ^ 9373639399224 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 178099148585257) ^ 1633937142984 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 178099148585257) ^ 49704 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_242757545720783 : Nat.Prime 242757545720783 := by
  apply lucas_primality 242757545720783 (5 : ZMod 242757545720783)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (311, 1), (1543, 1), (4146547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (311, 1), (1543, 1), (4146547, 1)] : List FactorBlock).map factorBlockValue).prod) = 242757545720783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_61
      · exact prime_seventyFourBT_311
      · exact prime_seventyFourBT_1543
      · exact prime_seventyFourBT_4146547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 242757545720783) ^ 121378772860391 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 242757545720783) ^ 3979631897062 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 242757545720783) ^ 780570886562 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 242757545720783) ^ 157328286274 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 242757545720783) ^ 58544506 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_336242142529523 : Nat.Prime 336242142529523 := by
  apply lucas_primality 336242142529523 (2 : ZMod 336242142529523)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (359, 1), (26723, 1), (372859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (359, 1), (26723, 1), (372859, 1)] : List FactorBlock).map factorBlockValue).prod) = 336242142529523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_47
      · exact prime_seventyFourBT_359
      · exact prime_seventyFourBT_26723
      · exact prime_seventyFourBT_372859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 336242142529523) ^ 168121071264761 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 336242142529523) ^ 7154088138926 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 336242142529523) ^ 936607639358 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 336242142529523) ^ 12582499814 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 336242142529523) ^ 901794358 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_379186449859369 : Nat.Prime 379186449859369 := by
  apply lucas_primality 379186449859369 (19 : ZMod 379186449859369)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (97, 1), (109, 1), (199, 1), (239, 1), (3491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (97, 1), (109, 1), (199, 1), (239, 1), (3491, 1)] : List FactorBlock).map factorBlockValue).prod) = 379186449859369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_97
      · exact prime_seventyFourBT_109
      · exact prime_seventyFourBT_199
      · exact prime_seventyFourBT_239
      · exact prime_seventyFourBT_3491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 379186449859369) ^ 189593224929684 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (19 : ZMod 379186449859369) ^ 126395483286456 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (19 : ZMod 379186449859369) ^ 3909138658344 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (19 : ZMod 379186449859369) ^ 3478774769352 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (19 : ZMod 379186449859369) ^ 1905459547032 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (19 : ZMod 379186449859369) ^ 1586554183512 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (19 : ZMod 379186449859369) ^ 108618289848 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_444082932196157 : Nat.Prime 444082932196157 := by
  apply lucas_primality 444082932196157 (2 : ZMod 444082932196157)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (307, 1), (1777, 1), (18500591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (307, 1), (1777, 1), (18500591, 1)] : List FactorBlock).map factorBlockValue).prod) = 444082932196157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_307
      · exact prime_seventyFourBT_1777
      · exact prime_seventyFourBT_18500591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 444082932196157) ^ 222041466098078 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 444082932196157) ^ 40371175654196 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 444082932196157) ^ 1446524209108 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 444082932196157) ^ 249905983228 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 444082932196157) ^ 24003716 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_532333269279499 : Nat.Prime 532333269279499 := by
  apply lucas_primality 532333269279499 (3 : ZMod 532333269279499)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (88722211546583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (88722211546583, 1)] : List FactorBlock).map factorBlockValue).prod) = 532333269279499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_88722211546583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 532333269279499) ^ 266166634639749 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 532333269279499) ^ 177444423093166 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 532333269279499) ^ 6 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_550829715065599 : Nat.Prime 550829715065599 := by
  apply lucas_primality 550829715065599 (7 : ZMod 550829715065599)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (337, 1), (2339, 1), (2741, 1), (42491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (337, 1), (2339, 1), (2741, 1), (42491, 1)] : List FactorBlock).map factorBlockValue).prod) = 550829715065599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_337
      · exact prime_seventyFourBT_2339
      · exact prime_seventyFourBT_2741
      · exact prime_seventyFourBT_42491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 550829715065599) ^ 275414857532799 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 550829715065599) ^ 183609905021866 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 550829715065599) ^ 1634509540254 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 550829715065599) ^ 235497954282 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 550829715065599) ^ 200959399878 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 550829715065599) ^ 12963444378 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_569729063855449 : Nat.Prime 569729063855449 := by
  apply lucas_primality 569729063855449 (31 : ZMod 569729063855449)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 2), (37, 1), (787, 1), (5545789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 2), (37, 1), (787, 1), (5545789, 1)] : List FactorBlock).map factorBlockValue).prod) = 569729063855449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_37
      · exact prime_seventyFourBT_787
      · exact prime_seventyFourBT_5545789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 569729063855449) ^ 284864531927724 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (31 : ZMod 569729063855449) ^ 189909687951816 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (31 : ZMod 569729063855449) ^ 81389866265064 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (31 : ZMod 569729063855449) ^ 15398082806904 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (31 : ZMod 569729063855449) ^ 723925112904 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (31 : ZMod 569729063855449) ^ 102731832 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_752069298704891 : Nat.Prime 752069298704891 := by
  apply lucas_primality 752069298704891 (2 : ZMod 752069298704891)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4224167, 1), (17803967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4224167, 1), (17803967, 1)] : List FactorBlock).map factorBlockValue).prod) = 752069298704891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_4224167
      · exact prime_seventyFourBT_17803967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 752069298704891) ^ 376034649352445 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 752069298704891) ^ 150413859740978 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 752069298704891) ^ 178039670 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 752069298704891) ^ 42241670 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_906212359866193 : Nat.Prime 906212359866193 := by
  apply lucas_primality 906212359866193 (5 : ZMod 906212359866193)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (131, 1), (144117741709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (131, 1), (144117741709, 1)] : List FactorBlock).map factorBlockValue).prod) = 906212359866193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_131
      · exact prime_seventyFourBT_144117741709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 906212359866193) ^ 453106179933096 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 906212359866193) ^ 302070786622064 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 906212359866193) ^ 6917651602032 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 906212359866193) ^ 6288 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1027827154875601 : Nat.Prime 1027827154875601 := by
  apply lucas_primality 1027827154875601 (14 : ZMod 1027827154875601)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 2), (95169181007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 2), (95169181007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1027827154875601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_95169181007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 1027827154875601) ^ 513913577437800 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 1027827154875601) ^ 342609051625200 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 1027827154875601) ^ 205565430975120 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 1027827154875601) ^ 10800 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1112672553244517 : Nat.Prime 1112672553244517 := by
  apply lucas_primality 1112672553244517 (2 : ZMod 1112672553244517)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (3697033, 1), (6840083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (3697033, 1), (6840083, 1)] : List FactorBlock).map factorBlockValue).prod) = 1112672553244517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_3697033
      · exact prime_seventyFourBT_6840083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1112672553244517) ^ 556336276622258 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1112672553244517) ^ 101152050294956 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1112672553244517) ^ 300963652 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1112672553244517) ^ 162669452 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1666594060360111 : Nat.Prime 1666594060360111 := by
  apply lucas_primality 1666594060360111 (11 : ZMod 1666594060360111)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (67, 1), (727, 1), (54310033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (67, 1), (727, 1), (54310033, 1)] : List FactorBlock).map factorBlockValue).prod) = 1666594060360111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_67
      · exact prime_seventyFourBT_727
      · exact prime_seventyFourBT_54310033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1666594060360111) ^ 833297030180055 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 1666594060360111) ^ 555531353453370 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 1666594060360111) ^ 333318812072022 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 1666594060360111) ^ 238084865765730 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 1666594060360111) ^ 24874538214330 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 1666594060360111) ^ 2292426492930 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 1666594060360111) ^ 30686670 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1891363373742541 : Nat.Prime 1891363373742541 := by
  apply lucas_primality 1891363373742541 (2 : ZMod 1891363373742541)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (479, 1), (65809442371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (479, 1), (65809442371, 1)] : List FactorBlock).map factorBlockValue).prod) = 1891363373742541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_479
      · exact prime_seventyFourBT_65809442371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1891363373742541) ^ 945681686871270 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1891363373742541) ^ 630454457914180 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1891363373742541) ^ 378272674748508 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1891363373742541) ^ 3948566542260 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1891363373742541) ^ 28740 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1924584213322399 : Nat.Prime 1924584213322399 := by
  apply lucas_primality 1924584213322399 (13 : ZMod 1924584213322399)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (3851, 1), (2251181059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (3851, 1), (2251181059, 1)] : List FactorBlock).map factorBlockValue).prod) = 1924584213322399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_37
      · exact prime_seventyFourBT_3851
      · exact prime_seventyFourBT_2251181059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1924584213322399) ^ 962292106661199 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 1924584213322399) ^ 641528071107466 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 1924584213322399) ^ 52015789549254 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 1924584213322399) ^ 499762195098 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 1924584213322399) ^ 854922 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_2292284255772179 : Nat.Prime 2292284255772179 := by
  apply lucas_primality 2292284255772179 (2 : ZMod 2292284255772179)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (269, 1), (4260751404781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (269, 1), (4260751404781, 1)] : List FactorBlock).map factorBlockValue).prod) = 2292284255772179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_269
      · exact prime_seventyFourBT_4260751404781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2292284255772179) ^ 1146142127886089 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2292284255772179) ^ 8521502809562 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2292284255772179) ^ 538 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_3267576397682183 : Nat.Prime 3267576397682183 := by
  apply lucas_primality 3267576397682183 (5 : ZMod 3267576397682183)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (96105188167123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (96105188167123, 1)] : List FactorBlock).map factorBlockValue).prod) = 3267576397682183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_17
      · exact prime_seventyFourBT_96105188167123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3267576397682183) ^ 1633788198841091 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 3267576397682183) ^ 192210376334246 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 3267576397682183) ^ 34 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_3847755780716929 : Nat.Prime 3847755780716929 := by
  apply lucas_primality 3847755780716929 (41 : ZMod 3847755780716929)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (347, 1), (28876649411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (347, 1), (28876649411, 1)] : List FactorBlock).map factorBlockValue).prod) = 3847755780716929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_347
      · exact prime_seventyFourBT_28876649411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (41 : ZMod 3847755780716929) ^ 1923877890358464 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (41 : ZMod 3847755780716929) ^ 1282585260238976 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (41 : ZMod 3847755780716929) ^ 11088633373824 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (41 : ZMod 3847755780716929) ^ 133248 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_4170556382260867 : Nat.Prime 4170556382260867 := by
  apply lucas_primality 4170556382260867 (2 : ZMod 4170556382260867)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19, 1), (67, 1), (42002098639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19, 1), (67, 1), (42002098639, 1)] : List FactorBlock).map factorBlockValue).prod) = 4170556382260867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_19
      · exact prime_seventyFourBT_67
      · exact prime_seventyFourBT_42002098639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4170556382260867) ^ 2085278191130433 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4170556382260867) ^ 1390185460753622 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4170556382260867) ^ 320812029404682 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4170556382260867) ^ 219502967487414 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4170556382260867) ^ 62247110182998 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4170556382260867) ^ 99294 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_4642738934583419 : Nat.Prime 4642738934583419 := by
  apply lucas_primality 4642738934583419 (2 : ZMod 4642738934583419)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (446827, 1), (5195230967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (446827, 1), (5195230967, 1)] : List FactorBlock).map factorBlockValue).prod) = 4642738934583419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_446827
      · exact prime_seventyFourBT_5195230967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4642738934583419) ^ 2321369467291709 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4642738934583419) ^ 10390461934 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4642738934583419) ^ 893654 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_8273815239896539 : Nat.Prime 8273815239896539 := by
  apply lucas_primality 8273815239896539 (10 : ZMod 8273815239896539)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1933, 1), (4657, 1), (6660221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1933, 1), (4657, 1), (6660221, 1)] : List FactorBlock).map factorBlockValue).prod) = 8273815239896539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_23
      · exact prime_seventyFourBT_1933
      · exact prime_seventyFourBT_4657
      · exact prime_seventyFourBT_6660221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 8273815239896539) ^ 4136907619948269 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 8273815239896539) ^ 2757938413298846 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 8273815239896539) ^ 359731097386806 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 8273815239896539) ^ 4280297589186 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 8273815239896539) ^ 1776640592634 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 8273815239896539) ^ 1242273378 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_8589271133023673 : Nat.Prime 8589271133023673 := by
  apply lucas_primality 8589271133023673 (3 : ZMod 8589271133023673)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (13, 1), (19, 1), (773, 1), (883, 1), (129967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (13, 1), (19, 1), (773, 1), (883, 1), (129967, 1)] : List FactorBlock).map factorBlockValue).prod) = 8589271133023673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_19
      · exact prime_seventyFourBT_773
      · exact prime_seventyFourBT_883
      · exact prime_seventyFourBT_129967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8589271133023673) ^ 4294635566511836 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8589271133023673) ^ 1227038733289096 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8589271133023673) ^ 660713164078744 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8589271133023673) ^ 452066901738088 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8589271133023673) ^ 11111605605464 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8589271133023673) ^ 9727373876584 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8589271133023673) ^ 66088092616 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_10617479489643581 : Nat.Prime 10617479489643581 := by
  apply lucas_primality 10617479489643581 (10 : ZMod 10617479489643581)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (83, 1), (5059, 1), (23173, 1), (54559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (83, 1), (5059, 1), (23173, 1), (54559, 1)] : List FactorBlock).map factorBlockValue).prod) = 10617479489643581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_83
      · exact prime_seventyFourBT_5059
      · exact prime_seventyFourBT_23173
      · exact prime_seventyFourBT_54559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10617479489643581) ^ 5308739744821790 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 10617479489643581) ^ 2123495897928716 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 10617479489643581) ^ 127921439634260 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 10617479489643581) ^ 2098730873620 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 10617479489643581) ^ 458183208460 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 10617479489643581) ^ 194605463620 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_14163637753311341 : Nat.Prime 14163637753311341 := by
  apply lucas_primality 14163637753311341 (2 : ZMod 14163637753311341)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (4951, 1), (20434021631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (4951, 1), (20434021631, 1)] : List FactorBlock).map factorBlockValue).prod) = 14163637753311341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_4951
      · exact prime_seventyFourBT_20434021631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14163637753311341) ^ 7081818876655670 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 14163637753311341) ^ 2832727550662268 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 14163637753311341) ^ 2023376821901620 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 14163637753311341) ^ 2860763028340 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 14163637753311341) ^ 693140 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_18161919774222373 : Nat.Prime 18161919774222373 := by
  apply lucas_primality 18161919774222373 (5 : ZMod 18161919774222373)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (21817, 1), (23124067081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (21817, 1), (23124067081, 1)] : List FactorBlock).map factorBlockValue).prod) = 18161919774222373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_21817
      · exact prime_seventyFourBT_23124067081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18161919774222373) ^ 9080959887111186 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 18161919774222373) ^ 6053973258074124 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 18161919774222373) ^ 832466414916 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 18161919774222373) ^ 785412 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_18976988525626081 : Nat.Prime 18976988525626081 := by
  apply lucas_primality 18976988525626081 (13 : ZMod 18976988525626081)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (1019, 1), (4310914051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (1019, 1), (4310914051, 1)] : List FactorBlock).map factorBlockValue).prod) = 18976988525626081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_1019
      · exact prime_seventyFourBT_4310914051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 18976988525626081) ^ 9488494262813040 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 18976988525626081) ^ 6325662841875360 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 18976988525626081) ^ 3795397705125216 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 18976988525626081) ^ 18623148700320 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 18976988525626081) ^ 4402080 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_27095623666590569 : Nat.Prime 27095623666590569 := by
  apply lucas_primality 27095623666590569 (3 : ZMod 27095623666590569)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11471, 1), (295262222851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11471, 1), (295262222851, 1)] : List FactorBlock).map factorBlockValue).prod) = 27095623666590569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_11471
      · exact prime_seventyFourBT_295262222851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 27095623666590569) ^ 13547811833295284 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 27095623666590569) ^ 2362097782808 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 27095623666590569) ^ 91768 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_28694005814996981 : Nat.Prime 28694005814996981 := by
  apply lucas_primality 28694005814996981 (2 : ZMod 28694005814996981)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (41, 1), (1521421305143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (41, 1), (1521421305143, 1)] : List FactorBlock).map factorBlockValue).prod) = 28694005814996981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_23
      · exact prime_seventyFourBT_41
      · exact prime_seventyFourBT_1521421305143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28694005814996981) ^ 14347002907498490 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28694005814996981) ^ 5738801162999396 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28694005814996981) ^ 1247565470217260 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28694005814996981) ^ 699853800365780 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28694005814996981) ^ 18860 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_42476646205044889 : Nat.Prime 42476646205044889 := by
  apply lucas_primality 42476646205044889 (11 : ZMod 42476646205044889)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (379, 1), (74797, 1), (62433199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (379, 1), (74797, 1), (62433199, 1)] : List FactorBlock).map factorBlockValue).prod) = 42476646205044889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_379
      · exact prime_seventyFourBT_74797
      · exact prime_seventyFourBT_62433199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 42476646205044889) ^ 21238323102522444 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 42476646205044889) ^ 14158882068348296 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 42476646205044889) ^ 112075583654472 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 42476646205044889) ^ 567892378104 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 42476646205044889) ^ 680353512 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_54191247333181139 : Nat.Prime 54191247333181139 := by
  apply lucas_primality 54191247333181139 (2 : ZMod 54191247333181139)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (27095623666590569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (27095623666590569, 1)] : List FactorBlock).map factorBlockValue).prod) = 54191247333181139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_27095623666590569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 54191247333181139) ^ 27095623666590569 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 54191247333181139) ^ 2 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_63300625179886267 : Nat.Prime 63300625179886267 := by
  apply lucas_primality 63300625179886267 (3 : ZMod 63300625179886267)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (167, 1), (13127, 1), (24113, 1), (199583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (167, 1), (13127, 1), (24113, 1), (199583, 1)] : List FactorBlock).map factorBlockValue).prod) = 63300625179886267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_167
      · exact prime_seventyFourBT_13127
      · exact prime_seventyFourBT_24113
      · exact prime_seventyFourBT_199583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 63300625179886267) ^ 31650312589943133 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 63300625179886267) ^ 21100208393295422 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 63300625179886267) ^ 379045659759798 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 63300625179886267) ^ 4822169968758 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 63300625179886267) ^ 2625165893082 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 63300625179886267) ^ 317164413702 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_72866488350242903 : Nat.Prime 72866488350242903 := by
  apply lucas_primality 72866488350242903 (5 : ZMod 72866488350242903)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (337, 1), (192917, 1), (80057017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (337, 1), (192917, 1), (80057017, 1)] : List FactorBlock).map factorBlockValue).prod) = 72866488350242903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_337
      · exact prime_seventyFourBT_192917
      · exact prime_seventyFourBT_80057017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 72866488350242903) ^ 36433244175121451 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 72866488350242903) ^ 10409498335748986 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 72866488350242903) ^ 216221033680246 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 72866488350242903) ^ 377709006206 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 72866488350242903) ^ 910182406 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_108971518645334239 : Nat.Prime 108971518645334239 := by
  apply lucas_primality 108971518645334239 (3 : ZMod 108971518645334239)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (18161919774222373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (18161919774222373, 1)] : List FactorBlock).map factorBlockValue).prod) = 108971518645334239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_18161919774222373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 108971518645334239) ^ 54485759322667119 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 108971518645334239) ^ 36323839548444746 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 108971518645334239) ^ 6 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_115913833613070487 : Nat.Prime 115913833613070487 := by
  apply lucas_primality 115913833613070487 (5 : ZMod 115913833613070487)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (5591, 1), (493624249913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (5591, 1), (493624249913, 1)] : List FactorBlock).map factorBlockValue).prod) = 115913833613070487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_5591
      · exact prime_seventyFourBT_493624249913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 115913833613070487) ^ 57956916806535243 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 115913833613070487) ^ 38637944537690162 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 115913833613070487) ^ 16559119087581498 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 115913833613070487) ^ 20732218496346 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 115913833613070487) ^ 234822 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_122413565146877203 : Nat.Prime 122413565146877203 := by
  apply lucas_primality 122413565146877203 (2 : ZMod 122413565146877203)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (17, 1), (1421711, 1), (6976421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (17, 1), (1421711, 1), (6976421, 1)] : List FactorBlock).map factorBlockValue).prod) = 122413565146877203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_17
      · exact prime_seventyFourBT_1421711
      · exact prime_seventyFourBT_6976421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 122413565146877203) ^ 61206782573438601 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 122413565146877203) ^ 40804521715625734 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 122413565146877203) ^ 11128505922443382 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 122413565146877203) ^ 7200797949816306 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 122413565146877203) ^ 86102987982 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 122413565146877203) ^ 17546757162 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_419789706112771763 : Nat.Prime 419789706112771763 := by
  apply lucas_primality 419789706112771763 (2 : ZMod 419789706112771763)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1433, 1), (146472332907457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1433, 1), (146472332907457, 1)] : List FactorBlock).map factorBlockValue).prod) = 419789706112771763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_1433
      · exact prime_seventyFourBT_146472332907457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 419789706112771763) ^ 209894853056385881 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 419789706112771763) ^ 292944665814914 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 419789706112771763) ^ 2866 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_453872282642891443 : Nat.Prime 453872282642891443 := by
  apply lucas_primality 453872282642891443 (2 : ZMod 453872282642891443)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (2292284255772179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (2292284255772179, 1)] : List FactorBlock).map factorBlockValue).prod) = 453872282642891443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_2292284255772179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 453872282642891443) ^ 226936141321445721 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 453872282642891443) ^ 151290760880963814 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 453872282642891443) ^ 41261116603899222 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 453872282642891443) ^ 198 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_654702207754413829 : Nat.Prime 654702207754413829 := by
  apply lucas_primality 654702207754413829 (6 : ZMod 654702207754413829)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3148051, 1), (17330887369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3148051, 1), (17330887369, 1)] : List FactorBlock).map factorBlockValue).prod) = 654702207754413829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_3148051
      · exact prime_seventyFourBT_17330887369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 654702207754413829) ^ 327351103877206914 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 654702207754413829) ^ 218234069251471276 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 654702207754413829) ^ 207970648428 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 654702207754413829) ^ 37776612 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1001085983121060029 : Nat.Prime 1001085983121060029 := by
  apply lucas_primality 1001085983121060029 (2 : ZMod 1001085983121060029)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2833, 1), (24107, 1), (3664558397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2833, 1), (24107, 1), (3664558397, 1)] : List FactorBlock).map factorBlockValue).prod) = 1001085983121060029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_2833
      · exact prime_seventyFourBT_24107
      · exact prime_seventyFourBT_3664558397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1001085983121060029) ^ 500542991560530014 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1001085983121060029) ^ 353366037105916 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1001085983121060029) ^ 41526775754804 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1001085983121060029) ^ 273180524 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_2436539249439778927 : Nat.Prime 2436539249439778927 := by
  apply lucas_primality 2436539249439778927 (3 : ZMod 2436539249439778927)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113, 1), (907, 1), (10169, 1), (389635199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113, 1), (907, 1), (10169, 1), (389635199, 1)] : List FactorBlock).map factorBlockValue).prod) = 2436539249439778927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_113
      · exact prime_seventyFourBT_907
      · exact prime_seventyFourBT_10169
      · exact prime_seventyFourBT_389635199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2436539249439778927) ^ 1218269624719889463 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2436539249439778927) ^ 812179749813259642 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2436539249439778927) ^ 21562294242829902 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2436539249439778927) ^ 2686371829591818 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2436539249439778927) ^ 239604607084254 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2436539249439778927) ^ 6253385874 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_2841502728802773043 : Nat.Prime 2841502728802773043 := by
  apply lucas_primality 2841502728802773043 (12 : ZMod 2841502728802773043)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (199, 1), (16189238304919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (199, 1), (16189238304919, 1)] : List FactorBlock).map factorBlockValue).prod) = 2841502728802773043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_199
      · exact prime_seventyFourBT_16189238304919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 2841502728802773043) ^ 1420751364401386521 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (12 : ZMod 2841502728802773043) ^ 947167576267591014 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (12 : ZMod 2841502728802773043) ^ 405928961257539006 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (12 : ZMod 2841502728802773043) ^ 14278908184938558 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (12 : ZMod 2841502728802773043) ^ 175518 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_3533293073331880357 : Nat.Prime 3533293073331880357 := by
  apply lucas_primality 3533293073331880357 (5 : ZMod 3533293073331880357)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8806613, 1), (33434089751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8806613, 1), (33434089751, 1)] : List FactorBlock).map factorBlockValue).prod) = 3533293073331880357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_8806613
      · exact prime_seventyFourBT_33434089751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3533293073331880357) ^ 1766646536665940178 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 3533293073331880357) ^ 1177764357777293452 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 3533293073331880357) ^ 401209077012 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 3533293073331880357) ^ 105679356 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_4219821668627836433 : Nat.Prime 4219821668627836433 := by
  apply lucas_primality 4219821668627836433 (3 : ZMod 4219821668627836433)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (43, 1), (2971, 1), (294920504287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (43, 1), (2971, 1), (294920504287, 1)] : List FactorBlock).map factorBlockValue).prod) = 4219821668627836433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_43
      · exact prime_seventyFourBT_2971
      · exact prime_seventyFourBT_294920504287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4219821668627836433) ^ 2109910834313918216 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4219821668627836433) ^ 602831666946833776 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4219821668627836433) ^ 98135387642507824 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4219821668627836433) ^ 1420337148646192 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4219821668627836433) ^ 14308336 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_6470651122999537031 : Nat.Prime 6470651122999537031 := by
  apply lucas_primality 6470651122999537031 (23 : ZMod 6470651122999537031)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (239, 1), (30323, 1), (5252051747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (239, 1), (30323, 1), (5252051747, 1)] : List FactorBlock).map factorBlockValue).prod) = 6470651122999537031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_17
      · exact prime_seventyFourBT_239
      · exact prime_seventyFourBT_30323
      · exact prime_seventyFourBT_5252051747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 6470651122999537031) ^ 3235325561499768515 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (23 : ZMod 6470651122999537031) ^ 1294130224599907406 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (23 : ZMod 6470651122999537031) ^ 380626536647031590 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (23 : ZMod 6470651122999537031) ^ 27073854071127770 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (23 : ZMod 6470651122999537031) ^ 213390862480610 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (23 : ZMod 6470651122999537031) ^ 1232023490 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_8329668916122871423 : Nat.Prime 8329668916122871423 := by
  apply lucas_primality 8329668916122871423 (5 : ZMod 8329668916122871423)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (41, 1), (79, 1), (5059, 1), (711957223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (41, 1), (79, 1), (5059, 1), (711957223, 1)] : List FactorBlock).map factorBlockValue).prod) = 8329668916122871423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_17
      · exact prime_seventyFourBT_41
      · exact prime_seventyFourBT_79
      · exact prime_seventyFourBT_5059
      · exact prime_seventyFourBT_711957223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8329668916122871423) ^ 4164834458061435711 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 8329668916122871423) ^ 2776556305374290474 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 8329668916122871423) ^ 1189952702303267346 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 8329668916122871423) ^ 489980524477815966 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 8329668916122871423) ^ 203162656490801742 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 8329668916122871423) ^ 105438847039530018 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 8329668916122871423) ^ 1646505023942058 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 8329668916122871423) ^ 11699676114 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_13100252586361266107 : Nat.Prime 13100252586361266107 := by
  apply lucas_primality 13100252586361266107 (2 : ZMod 13100252586361266107)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (4421, 1), (204667, 1), (658095089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (4421, 1), (204667, 1), (658095089, 1)] : List FactorBlock).map factorBlockValue).prod) = 13100252586361266107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_4421
      · exact prime_seventyFourBT_204667
      · exact prime_seventyFourBT_658095089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13100252586361266107) ^ 6550126293180633053 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 13100252586361266107) ^ 1190932053305569646 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 13100252586361266107) ^ 2963187646767986 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 13100252586361266107) ^ 64007644546318 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 13100252586361266107) ^ 19906321754 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_13270157605452595571 : Nat.Prime 13270157605452595571 := by
  apply lucas_primality 13270157605452595571 (6 : ZMod 13270157605452595571)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (137, 1), (27827, 1), (348088059343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (137, 1), (27827, 1), (348088059343, 1)] : List FactorBlock).map factorBlockValue).prod) = 13270157605452595571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_137
      · exact prime_seventyFourBT_27827
      · exact prime_seventyFourBT_348088059343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 13270157605452595571) ^ 6635078802726297785 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 13270157605452595571) ^ 2654031521090519114 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 13270157605452595571) ^ 96862464273376610 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 13270157605452595571) ^ 476880641299910 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 13270157605452595571) ^ 38122990 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_53045923195038963197 : Nat.Prime 53045923195038963197 := by
  apply lucas_primality 53045923195038963197 (2 : ZMod 53045923195038963197)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (83, 1), (293, 1), (77901939099703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (83, 1), (293, 1), (77901939099703, 1)] : List FactorBlock).map factorBlockValue).prod) = 53045923195038963197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_83
      · exact prime_seventyFourBT_293
      · exact prime_seventyFourBT_77901939099703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 53045923195038963197) ^ 26522961597519481598 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 53045923195038963197) ^ 7577989027862709028 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 53045923195038963197) ^ 639107508373963412 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 53045923195038963197) ^ 181044106467709772 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 53045923195038963197) ^ 680932 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_65841285665691048959 : Nat.Prime 65841285665691048959 := by
  apply lucas_primality 65841285665691048959 (19 : ZMod 65841285665691048959)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29587, 1), (1112672553244517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29587, 1), (1112672553244517, 1)] : List FactorBlock).map factorBlockValue).prod) = 65841285665691048959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_29587
      · exact prime_seventyFourBT_1112672553244517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 65841285665691048959) ^ 32920642832845524479 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (19 : ZMod 65841285665691048959) ^ 2225345106489034 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (19 : ZMod 65841285665691048959) ^ 59174 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_94944531214672579177 : Nat.Prime 94944531214672579177 := by
  apply lucas_primality 94944531214672579177 (5 : ZMod 94944531214672579177)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (79, 1), (197, 1), (3578903, 1), (6456881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (79, 1), (197, 1), (3578903, 1), (6456881, 1)] : List FactorBlock).map factorBlockValue).prod) = 94944531214672579177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_79
      · exact prime_seventyFourBT_197
      · exact prime_seventyFourBT_3578903
      · exact prime_seventyFourBT_6456881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 94944531214672579177) ^ 47472265607336289588 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 94944531214672579177) ^ 31648177071557526392 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 94944531214672579177) ^ 8631321019515689016 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 94944531214672579177) ^ 1201829509046488344 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 94944531214672579177) ^ 481951935099860808 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 94944531214672579177) ^ 26528947896792 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 94944531214672579177) ^ 14704395390696 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_131573119469748062059 : Nat.Prime 131573119469748062059 := by
  apply lucas_primality 131573119469748062059 (2 : ZMod 131573119469748062059)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (2436539249439778927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (2436539249439778927, 1)] : List FactorBlock).map factorBlockValue).prod) = 131573119469748062059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_2436539249439778927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 131573119469748062059) ^ 65786559734874031029 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 131573119469748062059) ^ 43857706489916020686 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 131573119469748062059) ^ 54 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_326242317315455873599 : Nat.Prime 326242317315455873599 := by
  apply lucas_primality 326242317315455873599 (6 : ZMod 326242317315455873599)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (2088679, 1), (3718941121061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (2088679, 1), (3718941121061, 1)] : List FactorBlock).map factorBlockValue).prod) = 326242317315455873599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_2088679
      · exact prime_seventyFourBT_3718941121061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 326242317315455873599) ^ 163121158657727936799 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 326242317315455873599) ^ 108747439105151957866 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 326242317315455873599) ^ 46606045330779410514 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 326242317315455873599) ^ 156195527084562 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 326242317315455873599) ^ 87724518 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_379727280497560020821 : Nat.Prime 379727280497560020821 := by
  apply lucas_primality 379727280497560020821 (2 : ZMod 379727280497560020821)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (654702207754413829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (654702207754413829, 1)] : List FactorBlock).map factorBlockValue).prod) = 379727280497560020821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_29
      · exact prime_seventyFourBT_654702207754413829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 379727280497560020821) ^ 189863640248780010410 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 379727280497560020821) ^ 75945456099512004164 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 379727280497560020821) ^ 13094044155088276580 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 379727280497560020821) ^ 580 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_510578919493072568401 : Nat.Prime 510578919493072568401 := by
  apply lucas_primality 510578919493072568401 (23 : ZMod 510578919493072568401)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (4517, 1), (94195800954371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (4517, 1), (94195800954371, 1)] : List FactorBlock).map factorBlockValue).prod) = 510578919493072568401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_4517
      · exact prime_seventyFourBT_94195800954371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 510578919493072568401) ^ 255289459746536284200 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (23 : ZMod 510578919493072568401) ^ 170192973164357522800 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (23 : ZMod 510578919493072568401) ^ 102115783898614513680 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (23 : ZMod 510578919493072568401) ^ 113034961145245200 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (23 : ZMod 510578919493072568401) ^ 5420400 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_588687307073926119463 : Nat.Prime 588687307073926119463 := by
  apply lucas_primality 588687307073926119463 (3 : ZMod 588687307073926119463)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (23, 1), (47, 1), (683, 1), (354323, 1), (1697053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (23, 1), (47, 1), (683, 1), (354323, 1), (1697053, 1)] : List FactorBlock).map factorBlockValue).prod) = 588687307073926119463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_17
      · exact prime_seventyFourBT_23
      · exact prime_seventyFourBT_47
      · exact prime_seventyFourBT_683
      · exact prime_seventyFourBT_354323
      · exact prime_seventyFourBT_1697053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 588687307073926119463) ^ 294343653536963059731 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 588687307073926119463) ^ 196229102357975373154 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 588687307073926119463) ^ 45283639005686624574 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 588687307073926119463) ^ 34628665121995654086 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 588687307073926119463) ^ 25595100307562005194 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 588687307073926119463) ^ 12525261852636725946 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 588687307073926119463) ^ 861914065994035314 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 588687307073926119463) ^ 1661442545569794 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 588687307073926119463) ^ 346887991756254 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1844905160359444879417 : Nat.Prime 1844905160359444879417 := by
  apply lucas_primality 1844905160359444879417 (5 : ZMod 1844905160359444879417)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (167, 1), (3371, 1), (35083, 1), (556023077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (167, 1), (3371, 1), (35083, 1), (556023077, 1)] : List FactorBlock).map factorBlockValue).prod) = 1844905160359444879417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_167
      · exact prime_seventyFourBT_3371
      · exact prime_seventyFourBT_35083
      · exact prime_seventyFourBT_556023077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1844905160359444879417) ^ 922452580179722439708 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1844905160359444879417) ^ 614968386786481626472 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1844905160359444879417) ^ 263557880051349268488 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1844905160359444879417) ^ 11047336289577514248 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1844905160359444879417) ^ 547287202717129896 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1844905160359444879417) ^ 52586870004259752 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1844905160359444879417) ^ 3318037032408 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1863853342980331365301 : Nat.Prime 1863853342980331365301 := by
  apply lucas_primality 1863853342980331365301 (6 : ZMod 1863853342980331365301)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (11, 1), (751, 1), (752069298704891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (11, 1), (751, 1), (752069298704891, 1)] : List FactorBlock).map factorBlockValue).prod) = 1863853342980331365301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_751
      · exact prime_seventyFourBT_752069298704891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1863853342980331365301) ^ 931926671490165682650 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1863853342980331365301) ^ 621284447660110455100 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1863853342980331365301) ^ 372770668596066273060 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1863853342980331365301) ^ 169441212998211942300 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1863853342980331365301) ^ 2481828685726140300 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1863853342980331365301) ^ 2478300 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_2506753909245863510281 : Nat.Prime 2506753909245863510281 := by
  apply lucas_primality 2506753909245863510281 (14 : ZMod 2506753909245863510281)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (2131, 1), (3267576397682183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (2131, 1), (3267576397682183, 1)] : List FactorBlock).map factorBlockValue).prod) = 2506753909245863510281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_2131
      · exact prime_seventyFourBT_3267576397682183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 2506753909245863510281) ^ 1253376954622931755140 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 2506753909245863510281) ^ 835584636415287836760 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 2506753909245863510281) ^ 501350781849172702056 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 2506753909245863510281) ^ 1176327503165585880 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 2506753909245863510281) ^ 767160 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_2669829410741951630377 : Nat.Prime 2669829410741951630377 := by
  apply lucas_primality 2669829410741951630377 (10 : ZMod 2669829410741951630377)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (19267, 1), (1924584213322399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (19267, 1), (1924584213322399, 1)] : List FactorBlock).map factorBlockValue).prod) = 2669829410741951630377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_19267
      · exact prime_seventyFourBT_1924584213322399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2669829410741951630377) ^ 1334914705370975815188 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2669829410741951630377) ^ 889943136913983876792 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2669829410741951630377) ^ 138570063359212728 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2669829410741951630377) ^ 1387224 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_3346460157093316443233 : Nat.Prime 3346460157093316443233 := by
  apply lucas_primality 3346460157093316443233 (3 : ZMod 3346460157093316443233)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (117703, 1), (68344692808409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (117703, 1), (68344692808409, 1)] : List FactorBlock).map factorBlockValue).prod) = 3346460157093316443233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_117703
      · exact prime_seventyFourBT_68344692808409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3346460157093316443233) ^ 1673230078546658221616 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3346460157093316443233) ^ 257420012084101264864 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3346460157093316443233) ^ 28431392208298144 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3346460157093316443233) ^ 48964448 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_4076844670487454486529 : Nat.Prime 4076844670487454486529 := by
  apply lucas_primality 4076844670487454486529 (7 : ZMod 4076844670487454486529)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 12), (3, 1), (61657, 1), (204431, 1), (26321693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 12), (3, 1), (61657, 1), (204431, 1), (26321693, 1)] : List FactorBlock).map factorBlockValue).prod) = 4076844670487454486529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_61657
      · exact prime_seventyFourBT_204431
      · exact prime_seventyFourBT_26321693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4076844670487454486529) ^ 2038422335243727243264 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 4076844670487454486529) ^ 1358948223495818162176 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 4076844670487454486529) ^ 66121359626440704 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 4076844670487454486529) ^ 19942399491698688 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 4076844670487454486529) ^ 154885351428096 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_6507294428366735928541 : Nat.Prime 6507294428366735928541 := by
  apply lucas_primality 6507294428366735928541 (2 : ZMod 6507294428366735928541)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (113, 1), (2621, 1), (4755684304529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (113, 1), (2621, 1), (4755684304529, 1)] : List FactorBlock).map factorBlockValue).prod) = 6507294428366735928541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_113
      · exact prime_seventyFourBT_2621
      · exact prime_seventyFourBT_4755684304529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6507294428366735928541) ^ 3253647214183367964270 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6507294428366735928541) ^ 2169098142788911976180 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6507294428366735928541) ^ 1301458885673347185708 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6507294428366735928541) ^ 929613489766676561220 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6507294428366735928541) ^ 591572220760612357140 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6507294428366735928541) ^ 57586676357227751580 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6507294428366735928541) ^ 2482752548022409740 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6507294428366735928541) ^ 1368319260 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_30002287154071092879457 : Nat.Prime 30002287154071092879457 := by
  apply lucas_primality 30002287154071092879457 (7 : ZMod 30002287154071092879457)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (97969601, 1), (354445348729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (97969601, 1), (354445348729, 1)] : List FactorBlock).map factorBlockValue).prod) = 30002287154071092879457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_97969601
      · exact prime_seventyFourBT_354445348729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 30002287154071092879457) ^ 15001143577035546439728 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 30002287154071092879457) ^ 10000762384690364293152 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 30002287154071092879457) ^ 306240781301856 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 30002287154071092879457) ^ 84645735264 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_48622241439958325402171 : Nat.Prime 48622241439958325402171 := by
  apply lucas_primality 48622241439958325402171 (2 : ZMod 48622241439958325402171)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (593, 1), (708913, 1), (502874374831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (593, 1), (708913, 1), (502874374831, 1)] : List FactorBlock).map factorBlockValue).prod) = 48622241439958325402171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_23
      · exact prime_seventyFourBT_593
      · exact prime_seventyFourBT_708913
      · exact prime_seventyFourBT_502874374831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 48622241439958325402171) ^ 24311120719979162701085 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 48622241439958325402171) ^ 9724448287991665080434 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 48622241439958325402171) ^ 2114010497389492408790 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 48622241439958325402171) ^ 81993661787450801690 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 48622241439958325402171) ^ 68587035983200090 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 48622241439958325402171) ^ 96688644070 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_94945118837588396402911 : Nat.Prime 94945118837588396402911 := by
  apply lucas_primality 94945118837588396402911 (3 : ZMod 94945118837588396402911)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1063273, 1), (3417671, 1), (870916159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1063273, 1), (3417671, 1), (870916159, 1)] : List FactorBlock).map factorBlockValue).prod) = 94945118837588396402911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_1063273
      · exact prime_seventyFourBT_3417671
      · exact prime_seventyFourBT_870916159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 94945118837588396402911) ^ 47472559418794198201455 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 94945118837588396402911) ^ 31648372945862798800970 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 94945118837588396402911) ^ 18989023767517679280582 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 94945118837588396402911) ^ 89295147001370670 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 94945118837588396402911) ^ 27780649113852210 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 94945118837588396402911) ^ 109017518915490 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_110176230366817140275669 : Nat.Prime 110176230366817140275669 := by
  apply lucas_primality 110176230366817140275669 (2 : ZMod 110176230366817140275669)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11910173269, 1), (2312649612193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11910173269, 1), (2312649612193, 1)] : List FactorBlock).map factorBlockValue).prod) = 110176230366817140275669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_11910173269
      · exact prime_seventyFourBT_2312649612193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 110176230366817140275669) ^ 55088115183408570137834 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 110176230366817140275669) ^ 9250598448772 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 110176230366817140275669) ^ 47640693076 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_180013722924426557276743 : Nat.Prime 180013722924426557276743 := by
  apply lucas_primality 180013722924426557276743 (5 : ZMod 180013722924426557276743)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (30002287154071092879457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (30002287154071092879457, 1)] : List FactorBlock).map factorBlockValue).prod) = 180013722924426557276743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_30002287154071092879457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 180013722924426557276743) ^ 90006861462213278638371 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 180013722924426557276743) ^ 60004574308142185758914 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 180013722924426557276743) ^ 6 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_217028181455033782737619 : Nat.Prime 217028181455033782737619 := by
  apply lucas_primality 217028181455033782737619 (3 : ZMod 217028181455033782737619)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (13, 1), (1845439469, 1), (15229531001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (13, 1), (1845439469, 1), (15229531001, 1)] : List FactorBlock).map factorBlockValue).prod) = 217028181455033782737619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_1845439469
      · exact prime_seventyFourBT_15229531001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 217028181455033782737619) ^ 108514090727516891368809 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 217028181455033782737619) ^ 72342727151677927579206 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 217028181455033782737619) ^ 19729834677730343885238 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 217028181455033782737619) ^ 16694475496541060210586 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 217028181455033782737619) ^ 117602438389722 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 217028181455033782737619) ^ 14250483579618 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_368412905199808202212643 : Nat.Prime 368412905199808202212643 := by
  apply lucas_primality 368412905199808202212643 (2 : ZMod 368412905199808202212643)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (1119397067, 1), (1509712241407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (1119397067, 1), (1509712241407, 1)] : List FactorBlock).map factorBlockValue).prod) = 368412905199808202212643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_109
      · exact prime_seventyFourBT_1119397067
      · exact prime_seventyFourBT_1509712241407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 368412905199808202212643) ^ 184206452599904101106321 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 368412905199808202212643) ^ 3379934910089983506538 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 368412905199808202212643) ^ 329117268626726 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 368412905199808202212643) ^ 244028560606 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_505943496551057445037247 : Nat.Prime 505943496551057445037247 := by
  apply lucas_primality 505943496551057445037247 (5 : ZMod 505943496551057445037247)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (443, 1), (13127, 1), (1891363373742541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (443, 1), (13127, 1), (1891363373742541, 1)] : List FactorBlock).map factorBlockValue).prod) = 505943496551057445037247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_23
      · exact prime_seventyFourBT_443
      · exact prime_seventyFourBT_13127
      · exact prime_seventyFourBT_1891363373742541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 505943496551057445037247) ^ 252971748275528722518623 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 505943496551057445037247) ^ 21997543328306845436402 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 505943496551057445037247) ^ 1142084642327443442522 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 505943496551057445037247) ^ 38542202830125500498 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 505943496551057445037247) ^ 267502006 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_636353217660429677820827 : Nat.Prime 636353217660429677820827 := by
  apply lucas_primality 636353217660429677820827 (2 : ZMod 636353217660429677820827)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (379, 1), (1931, 1), (2791, 1), (2192129, 1), (71059283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (379, 1), (1931, 1), (2791, 1), (2192129, 1), (71059283, 1)] : List FactorBlock).map factorBlockValue).prod) = 636353217660429677820827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_379
      · exact prime_seventyFourBT_1931
      · exact prime_seventyFourBT_2791
      · exact prime_seventyFourBT_2192129
      · exact prime_seventyFourBT_71059283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 636353217660429677820827) ^ 318176608830214838910413 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 636353217660429677820827) ^ 1679032236571054558894 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 636353217660429677820827) ^ 329545943894577772046 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 636353217660429677820827) ^ 228001869459129228886 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 636353217660429677820827) ^ 290290041170218394 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 636353217660429677820827) ^ 8955243999020222 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1634246449426698049759793 : Nat.Prime 1634246449426698049759793 := by
  apply lucas_primality 1634246449426698049759793 (3 : ZMod 1634246449426698049759793)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (43, 1), (179, 1), (13270157605452595571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (43, 1), (179, 1), (13270157605452595571, 1)] : List FactorBlock).map factorBlockValue).prod) = 1634246449426698049759793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_43
      · exact prime_seventyFourBT_179
      · exact prime_seventyFourBT_13270157605452595571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1634246449426698049759793) ^ 817123224713349024879896 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1634246449426698049759793) ^ 38005731382016233715344 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1634246449426698049759793) ^ 9129868432551385752848 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1634246449426698049759793) ^ 123152 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_2692759292816523650225939 : Nat.Prime 2692759292816523650225939 := by
  apply lucas_primality 2692759292816523650225939 (2 : ZMod 2692759292816523650225939)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (53, 1), (59627, 1), (93377, 1), (240134849173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (53, 1), (59627, 1), (93377, 1), (240134849173, 1)] : List FactorBlock).map factorBlockValue).prod) = 2692759292816523650225939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_19
      · exact prime_seventyFourBT_53
      · exact prime_seventyFourBT_59627
      · exact prime_seventyFourBT_93377
      · exact prime_seventyFourBT_240134849173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2692759292816523650225939) ^ 1346379646408261825112969 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2692759292816523650225939) ^ 141724173306132823696102 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2692759292816523650225939) ^ 50806779109745729249546 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2692759292816523650225939) ^ 45160066627811623094 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2692759292816523650225939) ^ 28837500592399880594 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2692759292816523650225939) ^ 11213529823306 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_3993415620942525716443343 : Nat.Prime 3993415620942525716443343 := by
  apply lucas_primality 3993415620942525716443343 (5 : ZMod 3993415620942525716443343)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (907, 1), (89917, 1), (411703, 1), (59467733903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (907, 1), (89917, 1), (411703, 1), (59467733903, 1)] : List FactorBlock).map factorBlockValue).prod) = 3993415620942525716443343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_907
      · exact prime_seventyFourBT_89917
      · exact prime_seventyFourBT_411703
      · exact prime_seventyFourBT_59467733903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3993415620942525716443343) ^ 1996707810471262858221671 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 3993415620942525716443343) ^ 4402883815813148529706 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 3993415620942525716443343) ^ 44412242634235191526 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 3993415620942525716443343) ^ 9699748656051876514 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 3993415620942525716443343) ^ 67152644952914 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_5302287843855082023990349 : Nat.Prime 5302287843855082023990349 := by
  apply lucas_primality 5302287843855082023990349 (2 : ZMod 5302287843855082023990349)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (438034841, 1), (336242142529523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (438034841, 1), (336242142529523, 1)] : List FactorBlock).map factorBlockValue).prod) = 5302287843855082023990349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_438034841
      · exact prime_seventyFourBT_336242142529523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5302287843855082023990349) ^ 2651143921927541011995174 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5302287843855082023990349) ^ 1767429281285027341330116 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5302287843855082023990349) ^ 12104717131062828 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5302287843855082023990349) ^ 15769254276 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_6545054943039489294220151 : Nat.Prime 6545054943039489294220151 := by
  apply lucas_primality 6545054943039489294220151 (17 : ZMod 6545054943039489294220151)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (107, 1), (135433, 1), (4806713, 1), (1879259801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (107, 1), (135433, 1), (4806713, 1), (1879259801, 1)] : List FactorBlock).map factorBlockValue).prod) = 6545054943039489294220151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_107
      · exact prime_seventyFourBT_135433
      · exact prime_seventyFourBT_4806713
      · exact prime_seventyFourBT_1879259801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 6545054943039489294220151) ^ 3272527471519744647110075 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (17 : ZMod 6545054943039489294220151) ^ 1309010988607897858844030 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (17 : ZMod 6545054943039489294220151) ^ 61168737785415787796450 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (17 : ZMod 6545054943039489294220151) ^ 48326884459766004550 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (17 : ZMod 6545054943039489294220151) ^ 1361648790564256550 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (17 : ZMod 6545054943039489294220151) ^ 3482783455250150 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_6925882633281258185231219 : Nat.Prime 6925882633281258185231219 := by
  apply lucas_primality 6925882633281258185231219 (2 : ZMod 6925882633281258185231219)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (227, 1), (39551, 1), (61027, 1), (80004182849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (227, 1), (39551, 1), (61027, 1), (80004182849, 1)] : List FactorBlock).map factorBlockValue).prod) = 6925882633281258185231219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_79
      · exact prime_seventyFourBT_227
      · exact prime_seventyFourBT_39551
      · exact prime_seventyFourBT_61027
      · exact prime_seventyFourBT_80004182849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6925882633281258185231219) ^ 3462941316640629092615609 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6925882633281258185231219) ^ 87669400421281749180142 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6925882633281258185231219) ^ 30510496181855762930534 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6925882633281258185231219) ^ 175112705956391954318 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6925882633281258185231219) ^ 113488826802583416934 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6925882633281258185231219) ^ 86569006602482 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_6971690925460901537639713 : Nat.Prime 6971690925460901537639713 := by
  apply lucas_primality 6971690925460901537639713 (5 : ZMod 6971690925460901537639713)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (24181, 1), (1001085983121060029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (24181, 1), (1001085983121060029, 1)] : List FactorBlock).map factorBlockValue).prod) = 6971690925460901537639713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_24181
      · exact prime_seventyFourBT_1001085983121060029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6971690925460901537639713) ^ 3485845462730450768819856 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 6971690925460901537639713) ^ 2323896975153633845879904 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 6971690925460901537639713) ^ 288312763138865288352 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 6971690925460901537639713) ^ 6964128 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_7266424370731632341847239 : Nat.Prime 7266424370731632341847239 := by
  apply lucas_primality 7266424370731632341847239 (11 : ZMod 7266424370731632341847239)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (9350729, 1), (183671503, 1), (192313967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (9350729, 1), (183671503, 1), (192313967, 1)] : List FactorBlock).map factorBlockValue).prod) = 7266424370731632341847239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_9350729
      · exact prime_seventyFourBT_183671503
      · exact prime_seventyFourBT_192313967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 7266424370731632341847239) ^ 3633212185365816170923619 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 7266424370731632341847239) ^ 660584033702875667440658 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 7266424370731632341847239) ^ 777097098069212822 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 7266424370731632341847239) ^ 39562067343302746 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (11 : ZMod 7266424370731632341847239) ^ 37784173890665114 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_12142643917225378680893929 : Nat.Prime 12142643917225378680893929 := by
  apply lucas_primality 12142643917225378680893929 (7 : ZMod 12142643917225378680893929)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (505943496551057445037247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (505943496551057445037247, 1)] : List FactorBlock).map factorBlockValue).prod) = 12142643917225378680893929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_505943496551057445037247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 12142643917225378680893929) ^ 6071321958612689340446964 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 12142643917225378680893929) ^ 4047547972408459560297976 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 12142643917225378680893929) ^ 24 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_82302680549020558227507769 : Nat.Prime 82302680549020558227507769 := by
  apply lucas_primality 82302680549020558227507769 (13 : ZMod 82302680549020558227507769)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (54727, 1), (6884639, 1), (9101645662069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (54727, 1), (6884639, 1), (9101645662069, 1)] : List FactorBlock).map factorBlockValue).prod) = 82302680549020558227507769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_54727
      · exact prime_seventyFourBT_6884639
      · exact prime_seventyFourBT_9101645662069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 82302680549020558227507769) ^ 41151340274510279113753884 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 82302680549020558227507769) ^ 27434226849673519409169256 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 82302680549020558227507769) ^ 1503877072542265394184 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 82302680549020558227507769) ^ 11954538291553203912 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (13 : ZMod 82302680549020558227507769) ^ 9042615325272 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_84284922373418933907361039 : Nat.Prime 84284922373418933907361039 := by
  apply lucas_primality 84284922373418933907361039 (6 : ZMod 84284922373418933907361039)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (11, 1), (23, 1), (67, 1), (730191503, 1), (42034199183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (11, 1), (23, 1), (67, 1), (730191503, 1), (42034199183, 1)] : List FactorBlock).map factorBlockValue).prod) = 84284922373418933907361039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_23
      · exact prime_seventyFourBT_67
      · exact prime_seventyFourBT_730191503
      · exact prime_seventyFourBT_42034199183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 84284922373418933907361039) ^ 42142461186709466953680519 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 84284922373418933907361039) ^ 28094974124472977969120346 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 84284922373418933907361039) ^ 7662265670310812173396458 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 84284922373418933907361039) ^ 3664561842322562343798306 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 84284922373418933907361039) ^ 1257983916021178118020314 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 84284922373418933907361039) ^ 115428517076867346 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 84284922373418933907361039) ^ 2005151139111186 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_101729941190242852785861347 : Nat.Prime 101729941190242852785861347 := by
  apply lucas_primality 101729941190242852785861347 (2 : ZMod 101729941190242852785861347)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (7266424370731632341847239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (7266424370731632341847239, 1)] : List FactorBlock).map factorBlockValue).prod) = 101729941190242852785861347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_7266424370731632341847239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 101729941190242852785861347) ^ 50864970595121426392930673 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 101729941190242852785861347) ^ 14532848741463264683694478 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 101729941190242852785861347) ^ 14 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_175678211693993681517752527 : Nat.Prime 175678211693993681517752527 := by
  apply lucas_primality 175678211693993681517752527 (3 : ZMod 175678211693993681517752527)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (127, 1), (170537, 1), (229902889, 1), (5880305411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (127, 1), (170537, 1), (229902889, 1), (5880305411, 1)] : List FactorBlock).map factorBlockValue).prod) = 175678211693993681517752527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_127
      · exact prime_seventyFourBT_170537
      · exact prime_seventyFourBT_229902889
      · exact prime_seventyFourBT_5880305411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 175678211693993681517752527) ^ 87839105846996840758876263 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 175678211693993681517752527) ^ 58559403897997893839250842 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 175678211693993681517752527) ^ 1383293005464517177305138 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 175678211693993681517752527) ^ 1030147192069719072798 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 175678211693993681517752527) ^ 764140948633288734 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 175678211693993681517752527) ^ 29875695123821466 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_242348336353487128520334511 : Nat.Prime 242348336353487128520334511 := by
  apply lucas_primality 242348336353487128520334511 (6 : ZMod 242348336353487128520334511)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (2692759292816523650225939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (2692759292816523650225939, 1)] : List FactorBlock).map factorBlockValue).prod) = 242348336353487128520334511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_2692759292816523650225939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 242348336353487128520334511) ^ 121174168176743564260167255 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 242348336353487128520334511) ^ 80782778784495709506778170 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 242348336353487128520334511) ^ 48469667270697425704066902 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 242348336353487128520334511) ^ 90 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_319298355560616253269491819 : Nat.Prime 319298355560616253269491819 := by
  apply lucas_primality 319298355560616253269491819 (2 : ZMod 319298355560616253269491819)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10513, 1), (10272879269, 1), (1478249829697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10513, 1), (10272879269, 1), (1478249829697, 1)] : List FactorBlock).map factorBlockValue).prod) = 319298355560616253269491819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_10513
      · exact prime_seventyFourBT_10272879269
      · exact prime_seventyFourBT_1478249829697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 319298355560616253269491819) ^ 159649177780308126634745909 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 319298355560616253269491819) ^ 30371764059794183702986 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 319298355560616253269491819) ^ 31081680919209122 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 319298355560616253269491819) ^ 215997559509994 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_361519625717391956181160159 : Nat.Prime 361519625717391956181160159 := by
  apply lucas_primality 361519625717391956181160159 (3 : ZMod 361519625717391956181160159)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (251, 1), (2477, 1), (3761, 1), (8589271133023673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (251, 1), (2477, 1), (3761, 1), (8589271133023673, 1)] : List FactorBlock).map factorBlockValue).prod) = 361519625717391956181160159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_251
      · exact prime_seventyFourBT_2477
      · exact prime_seventyFourBT_3761
      · exact prime_seventyFourBT_8589271133023673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 361519625717391956181160159) ^ 180759812858695978090580079 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 361519625717391956181160159) ^ 120506541905797318727053386 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 361519625717391956181160159) ^ 1440317233933832494745658 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 361519625717391956181160159) ^ 145950595768022590303254 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 361519625717391956181160159) ^ 96123271926985364578878 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 361519625717391956181160159) ^ 42089674446 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_375483903105617396548672783 : Nat.Prime 375483903105617396548672783 := by
  apply lucas_primality 375483903105617396548672783 (3 : ZMod 375483903105617396548672783)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (163, 1), (6507294428366735928541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (163, 1), (6507294428366735928541, 1)] : List FactorBlock).map factorBlockValue).prod) = 375483903105617396548672783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_59
      · exact prime_seventyFourBT_163
      · exact prime_seventyFourBT_6507294428366735928541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 375483903105617396548672783) ^ 187741951552808698274336391 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 375483903105617396548672783) ^ 125161301035205798849557594 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 375483903105617396548672783) ^ 6364133950942667738113098 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 375483903105617396548672783) ^ 2303582227641824518703514 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 375483903105617396548672783) ^ 57702 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_441857320321256835332529083 : Nat.Prime 441857320321256835332529083 := by
  apply lucas_primality 441857320321256835332529083 (2 : ZMod 441857320321256835332529083)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (251, 1), (2477, 1), (3761, 1), (8589271133023673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (251, 1), (2477, 1), (3761, 1), (8589271133023673, 1)] : List FactorBlock).map factorBlockValue).prod) = 441857320321256835332529083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_251
      · exact prime_seventyFourBT_2477
      · exact prime_seventyFourBT_3761
      · exact prime_seventyFourBT_8589271133023673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 441857320321256835332529083) ^ 220928660160628417666264541 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 441857320321256835332529083) ^ 40168847301932439575684462 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 441857320321256835332529083) ^ 1760387730363573049133582 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 441857320321256835332529083) ^ 178384061494249832592866 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 441857320321256835332529083) ^ 117483999021871001151962 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 441857320321256835332529083) ^ 51442935434 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1080095671896405597479515537 : Nat.Prime 1080095671896405597479515537 := by
  apply lucas_primality 1080095671896405597479515537 (5 : ZMod 1080095671896405597479515537)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (79, 1), (94945118837588396402911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (79, 1), (94945118837588396402911, 1)] : List FactorBlock).map factorBlockValue).prod) = 1080095671896405597479515537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_79
      · exact prime_seventyFourBT_94945118837588396402911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1080095671896405597479515537) ^ 540047835948202798739757768 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1080095671896405597479515537) ^ 360031890632135199159838512 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1080095671896405597479515537) ^ 13672097112612729082019184 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1080095671896405597479515537) ^ 11376 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_1388694435295378625330805689 : Nat.Prime 1388694435295378625330805689 := by
  apply lucas_primality 1388694435295378625330805689 (3 : ZMod 1388694435295378625330805689)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (16349153731, 1), (10617479489643581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (16349153731, 1), (10617479489643581, 1)] : List FactorBlock).map factorBlockValue).prod) = 1388694435295378625330805689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_16349153731
      · exact prime_seventyFourBT_10617479489643581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1388694435295378625330805689) ^ 694347217647689312665402844 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1388694435295378625330805689) ^ 84939835917148648 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1388694435295378625330805689) ^ 130793229848 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_2573169100694378041054139953 : Nat.Prime 2573169100694378041054139953 := by
  apply lucas_primality 2573169100694378041054139953 (7 : ZMod 2573169100694378041054139953)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (61, 1), (329102993, 1), (242757545720783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (61, 1), (329102993, 1), (242757545720783, 1)] : List FactorBlock).map factorBlockValue).prod) = 2573169100694378041054139953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_3
      · exact prime_seventyFourBT_11
      · exact prime_seventyFourBT_61
      · exact prime_seventyFourBT_329102993
      · exact prime_seventyFourBT_242757545720783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2573169100694378041054139953) ^ 1286584550347189020527069976 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2573169100694378041054139953) ^ 857723033564792680351379984 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2573169100694378041054139953) ^ 233924463699488912823103632 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2573169100694378041054139953) ^ 42183100011383246574658032 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2573169100694378041054139953) ^ 7818735032574978864 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2573169100694378041054139953) ^ 10599749198544 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_2733992169487776668620023701 : Nat.Prime 2733992169487776668620023701 := by
  apply lucas_primality 2733992169487776668620023701 (2 : ZMod 2733992169487776668620023701)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (23063, 1), (2397091, 1), (70647842899727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (23063, 1), (2397091, 1), (70647842899727, 1)] : List FactorBlock).map factorBlockValue).prod) = 2733992169487776668620023701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_23063
      · exact prime_seventyFourBT_2397091
      · exact prime_seventyFourBT_70647842899727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2733992169487776668620023701) ^ 1366996084743888334310011850 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2733992169487776668620023701) ^ 546798433897555333724004740 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2733992169487776668620023701) ^ 390570309926825238374289100 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2733992169487776668620023701) ^ 118544515869044645909900 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2733992169487776668620023701) ^ 1140545840557482660700 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2733992169487776668620023701) ^ 38698876813100 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_17497549884721770679168151681 : Nat.Prime 17497549884721770679168151681 := by
  apply lucas_primality 17497549884721770679168151681 (6 : ZMod 17497549884721770679168151681)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (7, 1), (23063, 1), (2397091, 1), (70647842899727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (7, 1), (23063, 1), (2397091, 1), (70647842899727, 1)] : List FactorBlock).map factorBlockValue).prod) = 17497549884721770679168151681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_23063
      · exact prime_seventyFourBT_2397091
      · exact prime_seventyFourBT_70647842899727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17497549884721770679168151681) ^ 8748774942360885339584075840 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 17497549884721770679168151681) ^ 3499509976944354135833630336 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 17497549884721770679168151681) ^ 2499649983531681525595450240 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 17497549884721770679168151681) ^ 758684901561885733823360 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 17497549884721770679168151681) ^ 7299493379567889028480 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (6 : ZMod 17497549884721770679168151681) ^ 247672811603840 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_29162583141202951131946919471 : Nat.Prime 29162583141202951131946919471 := by
  apply lucas_primality 29162583141202951131946919471 (14 : ZMod 29162583141202951131946919471)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (23, 1), (12907, 1), (5127750553, 1), (147367800443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (23, 1), (12907, 1), (5127750553, 1), (147367800443, 1)] : List FactorBlock).map factorBlockValue).prod) = 29162583141202951131946919471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_5
      · exact prime_seventyFourBT_13
      · exact prime_seventyFourBT_23
      · exact prime_seventyFourBT_12907
      · exact prime_seventyFourBT_5127750553
      · exact prime_seventyFourBT_147367800443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 29162583141202951131946919471) ^ 14581291570601475565973459735 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 29162583141202951131946919471) ^ 5832516628240590226389383894 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 29162583141202951131946919471) ^ 2243275626246380856303609190 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 29162583141202951131946919471) ^ 1267938397443606570954213890 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 29162583141202951131946919471) ^ 2259439307445800815987210 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 29162583141202951131946919471) ^ 5687207838950224990 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (14 : ZMod 29162583141202951131946919471) ^ 197889790398837290 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_43743874711804426697920379237 : Nat.Prime 43743874711804426697920379237 := by
  apply lucas_primality 43743874711804426697920379237 (2 : ZMod 43743874711804426697920379237)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (167, 1), (971, 1), (618883, 1), (108971518645334239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (167, 1), (971, 1), (618883, 1), (108971518645334239, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804426697920379237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_167
      · exact prime_seventyFourBT_971
      · exact prime_seventyFourBT_618883
      · exact prime_seventyFourBT_108971518645334239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43743874711804426697920379237) ^ 21871937355902213348960189618 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 43743874711804426697920379237) ^ 261939369531763034119283708 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 43743874711804426697920379237) ^ 45050334409685300409804716 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 43743874711804426697920379237) ^ 70681978195885856774092 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 43743874711804426697920379237) ^ 401424842524 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem prime_seventyFourBT_43743874711804426697920379243 : Nat.Prime 43743874711804426697920379243 := by
  apply lucas_primality 43743874711804426697920379243 (2 : ZMod 43743874711804426697920379243)
  · rw [← seventyFourBTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 1), (17627, 1), (4695503959, 1), (803213020193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 1), (17627, 1), (4695503959, 1), (803213020193, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804426697920379243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFourBT_2
      · exact prime_seventyFourBT_7
      · exact prime_seventyFourBT_47
      · exact prime_seventyFourBT_17627
      · exact prime_seventyFourBT_4695503959
      · exact prime_seventyFourBT_803213020193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43743874711804426697920379243) ^ 21871937355902213348960189621 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 43743874711804426697920379243) ^ 6249124958829203813988625606 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 43743874711804426697920379243) ^ 930720738549030355274901686 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 43743874711804426697920379243) ^ 2481640364883668616209246 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 43743874711804426697920379243) ^ 9316119226767843238 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide
    · change (2 : ZMod 43743874711804426697920379243) ^ 54461112571722794 ≠ 1
      rw [← seventyFourBTFastPow_eq_pow]
      decide

private theorem phi_seventyFourBT_87487749423608853395840758400 : Nat.totient 87487749423608853395840758400 = 29994486686816715256743014400 := by
  rw [← show ((([(2, 7), (5, 2), (7, 1), (23063, 1), (2397091, 1), (70647842899727, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_5, prime_seventyFourBT_7, prime_seventyFourBT_23063, prime_seventyFourBT_2397091, prime_seventyFourBT_70647842899727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758401 : Nat.totient 87487749423608853395840758401 = 53022871913704473930623491920 := by
  rw [← show ((([(3, 1), (11, 1), (8126303, 1), (326242317315455873599, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3, prime_seventyFourBT_11, prime_seventyFourBT_8126303, prime_seventyFourBT_326242317315455873599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758402 : Nat.totient 87487749423608853395840758402 = 41170705611110048656866239232 := by
  rw [← show ((([(2, 1), (17, 1), (2573169100694378041054139953, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_17, prime_seventyFourBT_2573169100694378041054139953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758403 : Nat.totient 87487749423608853395840758403 = 87453390231651227638273716000 := by
  rw [← show ((([(3023, 1), (16141, 1), (1414818131, 1), (1267295939291, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3023, prime_seventyFourBT_16141, prime_seventyFourBT_1414818131, prime_seventyFourBT_1267295939291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758404 : Nat.totient 87487749423608853395840758404 = 28156976824402726848980844160 := by
  rw [← show ((([(2, 2), (3, 1), (29, 1), (17749788803, 1), (14163637753311341, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_3, prime_seventyFourBT_29, prime_seventyFourBT_17749788803, prime_seventyFourBT_14163637753311341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758405 : Nat.totient 87487749423608853395840758405 = 69990199538887082716672606720 := by
  rw [← show ((([(5, 1), (17497549884721770679168151681, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_5, prime_seventyFourBT_17497549884721770679168151681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758406 : Nat.totient 87487749423608853395840758406 = 43424576356243810444650887248 := by
  rw [← show ((([(2, 1), (137, 1), (319298355560616253269491819, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_137, prime_seventyFourBT_319298355560616253269491819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758407 : Nat.totient 87487749423608853395840758407 = 49992999670633630511909004768 := by
  rw [← show ((([(3, 2), (7, 1), (1388694435295378625330805689, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3, prime_seventyFourBT_7, prime_seventyFourBT_1388694435295378625330805689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758408 : Nat.totient 87487749423608853395840758408 = 43716171181271301665179448016 := by
  rw [← show ((([(2, 3), (1579, 1), (6925882633281258185231219, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_1579, prime_seventyFourBT_6925882633281258185231219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758409 : Nat.totient 87487749423608853395840758409 = 87376572990312723490923712800 := by
  rw [← show ((([(787, 1), (8485801, 1), (13100252586361266107, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_787, prime_seventyFourBT_8485801, prime_seventyFourBT_13100252586361266107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758410 : Nat.totient 87487749423608853395840758410 = 20597526303001653530886248448 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (13, 1), (23, 1), (12907, 1), (5127750553, 1), (147367800443, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_3, prime_seventyFourBT_5, prime_seventyFourBT_13, prime_seventyFourBT_23, prime_seventyFourBT_12907, prime_seventyFourBT_5127750553, prime_seventyFourBT_147367800443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758411 : Nat.totient 87487749423608853395840758411 = 87487749423545551388561577312 := by
  rw [← show ((([(1382099294833, 1), (63300625179886267, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_1382099294833, prime_seventyFourBT_63300625179886267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758412 : Nat.totient 87487749423608853395840758412 = 39758927157601437793068432000 := by
  rw [← show ((([(2, 2), (11, 1), (4831, 1), (4242338953, 1), (97017966156511, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_11, prime_seventyFourBT_4831, prime_seventyFourBT_4242338953, prime_seventyFourBT_97017966156511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758413 : Nat.totient 87487749423608853395840758413 = 58325166282405902263893838940 := by
  rw [← show ((([(3, 1), (29162583141202951131946919471, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3, prime_seventyFourBT_29162583141202951131946919471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758414 : Nat.totient 87487749423608853395840758414 = 34653597971828512562313120000 := by
  rw [← show ((([(2, 1), (7, 3), (19, 1), (41, 1), (25301, 1), (6470651122999537031, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_7, prime_seventyFourBT_19, prime_seventyFourBT_41, prime_seventyFourBT_25301, prime_seventyFourBT_6470651122999537031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758415 : Nat.totient 87487749423608853395840758415 = 69990199538884680952200411072 := by
  rw [← show ((([(5, 1), (30712054193467, 1), (569729063855449, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_5, prime_seventyFourBT_30712054193467, prime_seventyFourBT_569729063855449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758416 : Nat.totient 87487749423608853395840758416 = 28793436519162407446732098240 := by
  rw [← show ((([(2, 4), (3, 6), (79, 1), (94945118837588396402911, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_3, prime_seventyFourBT_79, prime_seventyFourBT_94945118837588396402911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758417 : Nat.totient 87487749423608853395840758417 = 87481204368665813906546524900 := by
  rw [← show ((([(13367, 1), (6545054943039489294220151, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_13367, prime_seventyFourBT_6545054943039489294220151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758418 : Nat.totient 87487749423608853395840758418 = 43635201258705813752044896000 := by
  rw [← show ((([(2, 1), (1061, 1), (1123, 1), (1741, 1), (12653, 1), (1666594060360111, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_1061, prime_seventyFourBT_1123, prime_seventyFourBT_1741, prime_seventyFourBT_12653, prime_seventyFourBT_1666594060360111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758419 : Nat.totient 87487749423608853395840758419 = 54890699806903080167948651520 := by
  rw [← show ((([(3, 1), (17, 2), (15359, 1), (209042681, 1), (31428976639783, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3, prime_seventyFourBT_17, prime_seventyFourBT_15359, prime_seventyFourBT_209042681, prime_seventyFourBT_31428976639783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758420 : Nat.totient 87487749423608853395840758420 = 34181260239921598536049412256 := by
  rw [← show ((([(2, 2), (5, 1), (43, 1), (101729941190242852785861347, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_5, prime_seventyFourBT_43, prime_seventyFourBT_101729941190242852785861347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758421 : Nat.totient 87487749423608853395840758421 = 72568854708261229581009552000 := by
  rw [← show ((([(7, 1), (31, 1), (63467, 1), (149551, 1), (42476646205044889, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_7, prime_seventyFourBT_31, prime_seventyFourBT_63467, prime_seventyFourBT_149551, prime_seventyFourBT_42476646205044889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758422 : Nat.totient 87487749423608853395840758422 = 29154758460911341481020876128 := by
  rw [← show ((([(2, 1), (3, 1), (3727, 1), (367826603659, 1), (10636370686309, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_3, prime_seventyFourBT_3727, prime_seventyFourBT_367826603659, prime_seventyFourBT_10636370686309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758423 : Nat.totient 87487749423608853395840758423 = 73390249840834223970552902880 := by
  rw [← show ((([(11, 1), (13, 1), (2819, 1), (217028181455033782737619, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_11, prime_seventyFourBT_13, prime_seventyFourBT_2819, prime_seventyFourBT_217028181455033782737619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758424 : Nat.totient 87487749423608853395840758424 = 42561342161358512594647636224 := by
  rw [← show ((([(2, 3), (37, 1), (160207, 1), (1844905160359444879417, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_37, prime_seventyFourBT_160207, prime_seventyFourBT_1844905160359444879417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758425 : Nat.totient 87487749423608853395840758425 = 46216568913790659958543582080 := by
  rw [← show ((([(3, 2), (5, 2), (107, 1), (6173, 1), (588687307073926119463, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3, prime_seventyFourBT_5, prime_seventyFourBT_107, prime_seventyFourBT_6173, prime_seventyFourBT_588687307073926119463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758426 : Nat.totient 87487749423608853395840758426 = 43342554760208934914453068800 := by
  rw [← show ((([(2, 1), (109, 1), (390454707857, 1), (1027827154875601, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_109, prime_seventyFourBT_390454707857, prime_seventyFourBT_1027827154875601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758427 : Nat.totient 87487749423608853395840758427 = 85836891583884314907763922400 := by
  rw [← show ((([(53, 1), (589811, 1), (1611177559, 1), (1737061132691, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_53, prime_seventyFourBT_589811, prime_seventyFourBT_1611177559, prime_seventyFourBT_1737061132691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758428 : Nat.totient 87487749423608853395840758428 = 24985867551083899463319782400 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (2351, 1), (156424976273, 1), (2832104223829, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_3, prime_seventyFourBT_7, prime_seventyFourBT_2351, prime_seventyFourBT_156424976273, prime_seventyFourBT_2832104223829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758429 : Nat.totient 87487749423608853395840758429 = 86053520072744683069532463600 := by
  rw [← show ((([(61, 1), (21783071, 1), (65841285665691048959, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_61, prime_seventyFourBT_21783071, prime_seventyFourBT_65841285665691048959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758430 : Nat.totient 87487749423608853395840758430 = 34842234362000698655252737920 := by
  rw [← show ((([(2, 1), (5, 1), (229, 1), (720211, 1), (53045923195038963197, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_5, prime_seventyFourBT_229, prime_seventyFourBT_720211, prime_seventyFourBT_53045923195038963197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758431 : Nat.totient 87487749423608853395840758431 = 58315738480345347705512512704 := by
  rw [← show ((([(3, 1), (7243, 1), (42407, 1), (94944531214672579177, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3, prime_seventyFourBT_7243, prime_seventyFourBT_42407, prime_seventyFourBT_94944531214672579177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758432 : Nat.totient 87487749423608853395840758432 = 43743874711804426697920379200 := by
  rw [← show ((([(2, 5), (2733992169487776668620023701, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_2733992169487776668620023701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758433 : Nat.totient 87487749423608853395840758433 = 76529630949531264638287773696 := by
  rw [← show ((([(19, 1), (23, 1), (29, 1), (4813, 1), (372773, 1), (3847755780716929, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_19, prime_seventyFourBT_23, prime_seventyFourBT_29, prime_seventyFourBT_4813, prime_seventyFourBT_372773, prime_seventyFourBT_3847755780716929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758434 : Nat.totient 87487749423608853395840758434 = 26511439219275410119951744920 := by
  rw [← show ((([(2, 1), (3, 2), (11, 1), (441857320321256835332529083, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_3, prime_seventyFourBT_11, prime_seventyFourBT_441857320321256835332529083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758435 : Nat.totient 87487749423608853395840758435 = 59991599601822430560692618208 := by
  rw [← show ((([(5, 1), (7, 1), (20419713947, 1), (122413565146877203, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_5, prime_seventyFourBT_7, prime_seventyFourBT_20419713947, prime_seventyFourBT_122413565146877203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758436 : Nat.totient 87487749423608853395840758436 = 37991520507516274969505464320 := by
  rw [← show ((([(2, 2), (13, 1), (17, 1), (5279, 1), (7603, 1), (3410681, 1), (722964920857, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_13, prime_seventyFourBT_17, prime_seventyFourBT_5279, prime_seventyFourBT_7603, prime_seventyFourBT_3410681, prime_seventyFourBT_722964920857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758437 : Nat.totient 87487749423608853395840758437 = 56442809732531458848731108352 := by
  rw [← show ((([(3, 1), (47, 1), (89, 1), (6971690925460901537639713, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3, prime_seventyFourBT_47, prime_seventyFourBT_89, prime_seventyFourBT_6971690925460901537639713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758438 : Nat.totient 87487749423608853395840758438 = 43743874708271133612208015896 := by
  rw [← show ((([(2, 1), (12380482967, 1), (3533293073331880357, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_12380482967, prime_seventyFourBT_3533293073331880357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758439 : Nat.totient 87487749423608853395840758439 = 87112265520503235999292085424 := by
  rw [← show ((([(233, 1), (375483903105617396548672783, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_233, prime_seventyFourBT_375483903105617396548672783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758440 : Nat.totient 87487749423608853395840758440 = 23156907682808353095480545280 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (149, 1), (2423, 1), (3319, 1), (608611, 1), (999722038709, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_3, prime_seventyFourBT_5, prime_seventyFourBT_149, prime_seventyFourBT_2423, prime_seventyFourBT_3319, prime_seventyFourBT_608611, prime_seventyFourBT_999722038709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758441 : Nat.totient 87487749423608853395840758441 = 87487113070391192966162800132 := by
  rw [← show ((([(137483, 1), (636353217660429677820827, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_137483, prime_seventyFourBT_636353217660429677820827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758442 : Nat.totient 87487749423608853395840758442 = 36848702592828328225830782976 := by
  rw [← show ((([(2, 1), (7, 1), (59, 1), (4049, 1), (33563, 1), (107843, 1), (7227143649337, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_7, prime_seventyFourBT_59, prime_seventyFourBT_4049, prime_seventyFourBT_33563, prime_seventyFourBT_107843, prime_seventyFourBT_7227143649337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758443 : Nat.totient 87487749423608853395840758443 = 58325106046123074584180431872 := by
  rw [← show ((([(3, 3), (968273, 1), (3346460157093316443233, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3, prime_seventyFourBT_968273, prime_seventyFourBT_3346460157093316443233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758444 : Nat.totient 87487749423608853395840758444 = 43735887880562541646487481584 := by
  rw [← show ((([(2, 2), (5477, 1), (3993415620942525716443343, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_5477, prime_seventyFourBT_3993415620942525716443343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758445 : Nat.totient 87487749423608853395840758445 = 63141748369571969140648425600 := by
  rw [← show ((([(5, 1), (11, 1), (131, 1), (12142643917225378680893929, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_5, prime_seventyFourBT_11, prime_seventyFourBT_131, prime_seventyFourBT_12142643917225378680893929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758446 : Nat.totient 87487749423608853395840758446 = 28811226717814963768911414264 := by
  rw [← show ((([(2, 1), (3, 1), (83, 1), (175678211693993681517752527, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_3, prime_seventyFourBT_83, prime_seventyFourBT_175678211693993681517752527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758447 : Nat.totient 87487749423608853395840758447 = 87405446743059832837613249616 := by
  rw [← show ((([(1063, 1), (82302680549020558227507769, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_1063, prime_seventyFourBT_82302680549020558227507769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758448 : Nat.totient 87487749423608853395840758448 = 43743859406129356042112125952 := by
  rw [← show ((([(2, 4), (5358833, 1), (6124253, 1), (166611093709847, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_5358833, prime_seventyFourBT_6124253, prime_seventyFourBT_166611093709847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758449 : Nat.totient 87487749423608853395840758449 = 45204471228997838172795494400 := by
  rw [← show ((([(3, 1), (7, 1), (13, 1), (67, 1), (179, 1), (389539, 1), (633569, 1), (108270938051, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3, prime_seventyFourBT_7, prime_seventyFourBT_13, prime_seventyFourBT_67, prime_seventyFourBT_179, prime_seventyFourBT_389539, prime_seventyFourBT_633569, prime_seventyFourBT_108270938051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758450 : Nat.totient 87487749423608853395840758450 = 34457737341699792939751833600 := by
  rw [← show ((([(2, 1), (5, 2), (73, 1), (769, 1), (2633, 1), (19592581, 1), (604206691069, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_5, prime_seventyFourBT_73, prime_seventyFourBT_769, prime_seventyFourBT_2633, prime_seventyFourBT_19592581, prime_seventyFourBT_604206691069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758451 : Nat.totient 87487749423608853395840758451 = 87487627616622535909108390560 := by
  rw [← show ((([(718453, 1), (2530016107, 1), (48131078807381, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_718453, prime_seventyFourBT_2530016107, prime_seventyFourBT_48131078807381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758452 : Nat.totient 87487749423608853395840758452 = 26707230162016603890683155200 := by
  rw [← show ((([(2, 2), (3, 2), (19, 1), (31, 1), (919, 1), (156467, 1), (28694005814996981, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_3, prime_seventyFourBT_19, prime_seventyFourBT_31, prime_seventyFourBT_919, prime_seventyFourBT_156467, prime_seventyFourBT_28694005814996981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758453 : Nat.totient 87487749423608853395840758453 = 82341371114157549379883466240 := by
  rw [← show ((([(17, 1), (2052989, 1), (2506753909245863510281, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_17, prime_seventyFourBT_2052989, prime_seventyFourBT_2506753909245863510281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758454 : Nat.totient 87487749423608853395840758454 = 43743864699645614252767903584 := by
  rw [← show ((([(2, 1), (6901637, 1), (11906429, 1), (532333269279499, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_6901637, prime_seventyFourBT_11906429, prime_seventyFourBT_532333269279499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758455 : Nat.totient 87487749423608853395840758455 = 45519457861574396753732797440 := by
  rw [← show ((([(3, 1), (5, 1), (41, 1), (30557, 1), (40163, 1), (115913833613070487, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3, prime_seventyFourBT_5, prime_seventyFourBT_41, prime_seventyFourBT_30557, prime_seventyFourBT_40163, prime_seventyFourBT_115913833613070487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758456 : Nat.totient 87487749423608853395840758456 = 32347404785175474723555657600 := by
  rw [← show ((([(2, 3), (7, 1), (11, 1), (23, 1), (127, 1), (48622241439958325402171, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_7, prime_seventyFourBT_11, prime_seventyFourBT_23, prime_seventyFourBT_127, prime_seventyFourBT_48622241439958325402171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758457 : Nat.totient 87487749423608853395840758457 = 87392839657886387757299752992 := by
  rw [← show ((([(947, 1), (34603, 1), (2669829410741951630377, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_947, prime_seventyFourBT_34603, prime_seventyFourBT_2669829410741951630377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758458 : Nat.totient 87487749423608853395840758458 = 29162223113757102278832204000 := by
  rw [← show ((([(2, 1), (3, 1), (81001, 1), (180013722924426557276743, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_3, prime_seventyFourBT_81001, prime_seventyFourBT_180013722924426557276743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758459 : Nat.totient 87487749423608853395840758459 = 87479070952007925891542124000 := by
  rw [← show ((([(10607, 1), (206351, 1), (13622341, 1), (2934244846207, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_10607, prime_seventyFourBT_206351, prime_seventyFourBT_13622341, prime_seventyFourBT_2934244846207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758460 : Nat.totient 87487749423608853395840758460 = 34916010773652513626204160000 := by
  rw [← show ((([(2, 2), (5, 1), (461, 1), (18553, 1), (26951, 1), (18976988525626081, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_5, prime_seventyFourBT_461, prime_seventyFourBT_18553, prime_seventyFourBT_26951, prime_seventyFourBT_18976988525626081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758461 : Nat.totient 87487749423608853395840758461 = 56748798825337261372301827200 := by
  rw [← show ((([(3, 2), (37, 1), (4895207, 1), (3829246411, 1), (14015824021, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3, prime_seventyFourBT_37, prime_seventyFourBT_4895207, prime_seventyFourBT_3829246411, prime_seventyFourBT_14015824021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758462 : Nat.totient 87487749423608853395840758462 = 38437476490515938130350307840 := by
  rw [← show ((([(2, 1), (13, 1), (29, 1), (71, 1), (1634246449426698049759793, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_13, prime_seventyFourBT_29, prime_seventyFourBT_71, prime_seventyFourBT_1634246449426698049759793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758463 : Nat.totient 87487749423608853395840758463 = 73245542963438885956281647856 := by
  rw [← show ((([(7, 2), (43, 1), (4984883, 1), (8329668916122871423, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_7, prime_seventyFourBT_43, prime_seventyFourBT_4984883, prime_seventyFourBT_8329668916122871423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758464 : Nat.totient 87487749423608853395840758464 = 29087590685249135697307107328 := by
  rw [← show ((([(2, 6), (3, 1), (389, 1), (1314233, 1), (12969857, 1), (68720903213, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_3, prime_seventyFourBT_389, prime_seventyFourBT_1314233, prime_seventyFourBT_12969857, prime_seventyFourBT_68720903213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758465 : Nat.totient 87487749423608853395840758465 = 69990194806404577023085470976 := by
  rw [← show ((([(5, 1), (21885317, 1), (45613013, 1), (17528132113733, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_5, prime_seventyFourBT_21885317, prime_seventyFourBT_45613013, prime_seventyFourBT_17528132113733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758466 : Nat.totient 87487749423608853395840758466 = 43742473361831476522877549664 := by
  rw [← show ((([(2, 1), (31513, 1), (3306707, 1), (419789706112771763, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_31513, prime_seventyFourBT_3306707, prime_seventyFourBT_419789706112771763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758467 : Nat.totient 87487749423608853395840758467 = 52745271468262609752448951200 := by
  rw [← show ((([(3, 1), (11, 1), (191, 1), (190489963, 1), (72866488350242903, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3, prime_seventyFourBT_11, prime_seventyFourBT_191, prime_seventyFourBT_190489963, prime_seventyFourBT_72866488350242903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758468 : Nat.totient 87487749423608853395840758468 = 43647694325496605386468651680 := by
  rw [← show ((([(2, 2), (743, 1), (1171, 1), (29673934067, 1), (847161902767, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_743, prime_seventyFourBT_1171, prime_seventyFourBT_29673934067, prime_seventyFourBT_847161902767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758469 : Nat.totient 87487749423608853395840758469 = 87167763719380146560460595200 := by
  rw [← show ((([(293, 1), (4397, 1), (97879, 1), (241979, 1), (286801, 1), (9997129, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_293, prime_seventyFourBT_4397, prime_seventyFourBT_97879, prime_seventyFourBT_241979, prime_seventyFourBT_286801, prime_seventyFourBT_9997129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758470 : Nat.totient 87487749423608853395840758470 = 18813698172177149542219776000 := by
  rw [← show ((([(2, 1), (3, 3), (5, 1), (7, 1), (17, 1), (4987, 1), (5501, 1), (16294513, 1), (6091357949, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_3, prime_seventyFourBT_5, prime_seventyFourBT_7, prime_seventyFourBT_17, prime_seventyFourBT_4987, prime_seventyFourBT_5501, prime_seventyFourBT_16294513, prime_seventyFourBT_6091357949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758471 : Nat.totient 87487749423608853395840758471 = 82883131032892597953954402420 := by
  rw [← show ((([(19, 2), (242348336353487128520334511, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_19, prime_seventyFourBT_242348336353487128520334511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758472 : Nat.totient 87487749423608853395840758472 = 43437084583968743999464457280 := by
  rw [← show ((([(2, 3), (167, 1), (971, 1), (618883, 1), (108971518645334239, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_167, prime_seventyFourBT_971, prime_seventyFourBT_618883, prime_seventyFourBT_108971518645334239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758473 : Nat.totient 87487749423608853395840758473 = 58141092067366618511181792576 := by
  rw [← show ((([(3, 1), (317, 1), (699197, 1), (131573119469748062059, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3, prime_seventyFourBT_317, prime_seventyFourBT_699197, prime_seventyFourBT_131573119469748062059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758474 : Nat.totient 87487749423608853395840758474 = 43743874711804426697920379236 := by
  rw [← show ((([(2, 1), (43743874711804426697920379237, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_43743874711804426697920379237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758475 : Nat.totient 87487749423608853395840758475 = 64580710768151422998703334400 := by
  rw [← show ((([(5, 2), (13, 1), (2521, 1), (41921029019, 1), (2547176876197, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_5, prime_seventyFourBT_13, prime_seventyFourBT_2521, prime_seventyFourBT_41921029019, prime_seventyFourBT_2547176876197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758476 : Nat.totient 87487749423608853395840758476 = 29160347251888617944576731776 := by
  rw [← show ((([(2, 2), (3, 1), (13043, 1), (3138532723, 1), (178099148585257, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_3, prime_seventyFourBT_13043, prime_seventyFourBT_3138532723, prime_seventyFourBT_178099148585257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758477 : Nat.totient 87487749423608853395840758477 = 74973773255848172499282038784 := by
  rw [← show ((([(7, 1), (5417, 1), (45553, 1), (316363, 1), (160098661169897, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_7, prime_seventyFourBT_5417, prime_seventyFourBT_45553, prime_seventyFourBT_316363, prime_seventyFourBT_160098661169897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758478 : Nat.totient 87487749423608853395840758478 = 39767158828913115179927617380 := by
  rw [← show ((([(2, 1), (11, 2), (361519625717391956181160159, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_11, prime_seventyFourBT_361519625717391956181160159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758479 : Nat.totient 87487749423608853395840758479 = 55784963645050305402326154048 := by
  rw [← show ((([(3, 2), (23, 1), (12899, 1), (73783079, 1), (444082932196157, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3, prime_seventyFourBT_23, prime_seventyFourBT_12899, prime_seventyFourBT_73783079, prime_seventyFourBT_444082932196157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758480 : Nat.totient 87487749423608853395840758480 = 34300785386372426819522666496 := by
  rw [← show ((([(2, 4), (5, 1), (53, 1), (1009, 1), (37125547, 1), (550829715065599, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_5, prime_seventyFourBT_53, prime_seventyFourBT_1009, prime_seventyFourBT_37125547, prime_seventyFourBT_550829715065599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758481 : Nat.totient 87487749423608853395840758481 = 87487747559755510415462454000 := by
  rw [← show ((([(46939181, 1), (1863853342980331365301, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_46939181, prime_seventyFourBT_1863853342980331365301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758482 : Nat.totient 87487749423608853395840758482 = 28994013296456113264132197072 := by
  rw [← show ((([(2, 1), (3, 1), (173, 1), (84284922373418933907361039, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_3, prime_seventyFourBT_173, prime_seventyFourBT_84284922373418933907361039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758483 : Nat.totient 87487749423608853395840758483 = 84665563958082923757437756040 := by
  rw [← show ((([(31, 1), (341098439287, 1), (8273815239896539, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_31, prime_seventyFourBT_341098439287, prime_seventyFourBT_8273815239896539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758484 : Nat.totient 87487749423608853395840758484 = 36694907249638846276853148672 := by
  rw [← show ((([(2, 2), (7, 1), (47, 1), (17627, 1), (4695503959, 1), (803213020193, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_7, prime_seventyFourBT_47, prime_seventyFourBT_17627, prime_seventyFourBT_4695503959, prime_seventyFourBT_803213020193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758485 : Nat.totient 87487749423608853395840758485 = 46551871295170369366396656960 := by
  rw [← show ((([(3, 1), (5, 1), (431, 1), (29815703, 1), (453872282642891443, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3, prime_seventyFourBT_5, prime_seventyFourBT_431, prime_seventyFourBT_29815703, prime_seventyFourBT_453872282642891443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758486 : Nat.totient 87487749423608853395840758486 = 43743874711804426697920379242 := by
  rw [← show ((([(2, 1), (43743874711804426697920379243, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_43743874711804426697920379243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758487 : Nat.totient 87487749423608853395840758487 = 82013357772484900415259696000 := by
  rw [← show ((([(17, 1), (251, 1), (4416216319, 1), (4642738934583419, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_17, prime_seventyFourBT_251, prime_seventyFourBT_4416216319, prime_seventyFourBT_4642738934583419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758488 : Nat.totient 87487749423608853395840758488 = 26535366591268743761913446400 := by
  rw [← show ((([(2, 3), (3, 2), (13, 1), (101, 1), (227, 1), (4076844670487454486529, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_3, prime_seventyFourBT_13, prime_seventyFourBT_101, prime_seventyFourBT_227, prime_seventyFourBT_4076844670487454486529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758489 : Nat.totient 87487749423608853395840758489 = 78665080946873576026179409920 := by
  rw [← show ((([(11, 1), (97, 1), (1597, 1), (12310733, 1), (4170556382260867, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_11, prime_seventyFourBT_97, prime_seventyFourBT_1597, prime_seventyFourBT_12310733, prime_seventyFourBT_4170556382260867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758490 : Nat.totient 87487749423608853395840758490 = 32608960489777558582934784000 := by
  rw [← show ((([(2, 1), (5, 1), (19, 1), (61, 1), (42013, 1), (1646947, 1), (109093905910601, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_5, prime_seventyFourBT_19, prime_seventyFourBT_61, prime_seventyFourBT_42013, prime_seventyFourBT_1646947, prime_seventyFourBT_109093905910601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758491 : Nat.totient 87487749423608853395840758491 = 47787457047683848467170042880 := by
  rw [← show ((([(3, 1), (7, 1), (29, 1), (103, 1), (3673, 1), (379727280497560020821, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3, prime_seventyFourBT_7, prime_seventyFourBT_29, prime_seventyFourBT_103, prime_seventyFourBT_3673, prime_seventyFourBT_379727280497560020821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758492 : Nat.totient 87487749423608853395840758492 = 43619954348691168997919310336 := by
  rw [← show ((([(2, 2), (353, 1), (1143361069, 1), (54191247333181139, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_353, prime_seventyFourBT_1143361069, prime_seventyFourBT_54191247333181139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758493 : Nat.totient 87487749423608853395840758493 = 86705129211990239506067656704 := by
  rw [← show ((([(113, 1), (10333, 1), (197601193, 1), (379186449859369, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_113, prime_seventyFourBT_10333, prime_seventyFourBT_197601193, prime_seventyFourBT_379186449859369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758494 : Nat.totient 87487749423608853395840758494 = 29162583135519945664078288728 := by
  rw [← show ((([(2, 1), (3, 1), (5131542343, 1), (2841502728802773043, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_3, prime_seventyFourBT_5131542343, prime_seventyFourBT_2841502728802773043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758495 : Nat.totient 87487749423608853395840758495 = 69104247645706963359749374464 := by
  rw [← show ((([(5, 1), (79, 1), (244410673517, 1), (906212359866193, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_5, prime_seventyFourBT_79, prime_seventyFourBT_244410673517, prime_seventyFourBT_906212359866193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758496 : Nat.totient 87487749423608853395840758496 = 42441166679017904894896358400 := by
  rw [← show ((([(2, 5), (41, 1), (181, 1), (368412905199808202212643, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_41, prime_seventyFourBT_181, prime_seventyFourBT_368412905199808202212643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758497 : Nat.totient 87487749423608853395840758497 = 58325166282405902263893838944 := by
  rw [← show ((([(3, 4), (1080095671896405597479515537, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_3, prime_seventyFourBT_1080095671896405597479515537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758498 : Nat.totient 87487749423608853395840758498 = 36481377226548466157513524992 := by
  rw [← show ((([(2, 1), (7, 1), (37, 1), (40024267, 1), (4219821668627836433, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_7, prime_seventyFourBT_37, prime_seventyFourBT_40024267, prime_seventyFourBT_4219821668627836433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758499 : Nat.totient 87487749423608853395840758499 = 87487639247378486578699688760 := by
  rw [← show ((([(794071, 1), (110176230366817140275669, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_794071, prime_seventyFourBT_110176230366817140275669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758500 : Nat.totient 87487749423608853395840758500 = 21209151375420328095961392000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 3), (11, 1), (5302287843855082023990349, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_2, prime_seventyFourBT_3, prime_seventyFourBT_5, prime_seventyFourBT_11, prime_seventyFourBT_5302287843855082023990349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFourBT_87487749423608853395840758501 : Nat.totient 87487749423608853395840758501 = 79388788833723612956284972800 := by
  rw [← show ((([(13, 1), (59, 1), (223403, 1), (510578919493072568401, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608853395840758501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFourBT_13, prime_seventyFourBT_59, prime_seventyFourBT_223403, prime_seventyFourBT_510578919493072568401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SeventyFourBT : certifiedKill 1 87487749423608853395840758399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_seventyFourBT_87487749423608853395840758400, phi_seventyFourBT_87487749423608853395840758401, phi_seventyFourBT_87487749423608853395840758402,
    phi_seventyFourBT_87487749423608853395840758403, phi_seventyFourBT_87487749423608853395840758404, phi_seventyFourBT_87487749423608853395840758405,
    phi_seventyFourBT_87487749423608853395840758406, phi_seventyFourBT_87487749423608853395840758407, phi_seventyFourBT_87487749423608853395840758408,
    phi_seventyFourBT_87487749423608853395840758409, phi_seventyFourBT_87487749423608853395840758410, phi_seventyFourBT_87487749423608853395840758411,
    phi_seventyFourBT_87487749423608853395840758412, phi_seventyFourBT_87487749423608853395840758413, phi_seventyFourBT_87487749423608853395840758414,
    phi_seventyFourBT_87487749423608853395840758415, phi_seventyFourBT_87487749423608853395840758416, phi_seventyFourBT_87487749423608853395840758417,
    phi_seventyFourBT_87487749423608853395840758418, phi_seventyFourBT_87487749423608853395840758419, phi_seventyFourBT_87487749423608853395840758420,
    phi_seventyFourBT_87487749423608853395840758421, phi_seventyFourBT_87487749423608853395840758422, phi_seventyFourBT_87487749423608853395840758423,
    phi_seventyFourBT_87487749423608853395840758424, phi_seventyFourBT_87487749423608853395840758425, phi_seventyFourBT_87487749423608853395840758426,
    phi_seventyFourBT_87487749423608853395840758427, phi_seventyFourBT_87487749423608853395840758428, phi_seventyFourBT_87487749423608853395840758429,
    phi_seventyFourBT_87487749423608853395840758430, phi_seventyFourBT_87487749423608853395840758431, phi_seventyFourBT_87487749423608853395840758432,
    phi_seventyFourBT_87487749423608853395840758433, phi_seventyFourBT_87487749423608853395840758434, phi_seventyFourBT_87487749423608853395840758435,
    phi_seventyFourBT_87487749423608853395840758436, phi_seventyFourBT_87487749423608853395840758437, phi_seventyFourBT_87487749423608853395840758438,
    phi_seventyFourBT_87487749423608853395840758439, phi_seventyFourBT_87487749423608853395840758440, phi_seventyFourBT_87487749423608853395840758441,
    phi_seventyFourBT_87487749423608853395840758442, phi_seventyFourBT_87487749423608853395840758443, phi_seventyFourBT_87487749423608853395840758444,
    phi_seventyFourBT_87487749423608853395840758445, phi_seventyFourBT_87487749423608853395840758446, phi_seventyFourBT_87487749423608853395840758447,
    phi_seventyFourBT_87487749423608853395840758448, phi_seventyFourBT_87487749423608853395840758449, phi_seventyFourBT_87487749423608853395840758450,
    phi_seventyFourBT_87487749423608853395840758451, phi_seventyFourBT_87487749423608853395840758452, phi_seventyFourBT_87487749423608853395840758453,
    phi_seventyFourBT_87487749423608853395840758454, phi_seventyFourBT_87487749423608853395840758455, phi_seventyFourBT_87487749423608853395840758456,
    phi_seventyFourBT_87487749423608853395840758457, phi_seventyFourBT_87487749423608853395840758458, phi_seventyFourBT_87487749423608853395840758459,
    phi_seventyFourBT_87487749423608853395840758460, phi_seventyFourBT_87487749423608853395840758461, phi_seventyFourBT_87487749423608853395840758462,
    phi_seventyFourBT_87487749423608853395840758463, phi_seventyFourBT_87487749423608853395840758464, phi_seventyFourBT_87487749423608853395840758465,
    phi_seventyFourBT_87487749423608853395840758466, phi_seventyFourBT_87487749423608853395840758467, phi_seventyFourBT_87487749423608853395840758468,
    phi_seventyFourBT_87487749423608853395840758469, phi_seventyFourBT_87487749423608853395840758470, phi_seventyFourBT_87487749423608853395840758471,
    phi_seventyFourBT_87487749423608853395840758472, phi_seventyFourBT_87487749423608853395840758473, phi_seventyFourBT_87487749423608853395840758474,
    phi_seventyFourBT_87487749423608853395840758475, phi_seventyFourBT_87487749423608853395840758476, phi_seventyFourBT_87487749423608853395840758477,
    phi_seventyFourBT_87487749423608853395840758478, phi_seventyFourBT_87487749423608853395840758479, phi_seventyFourBT_87487749423608853395840758480,
    phi_seventyFourBT_87487749423608853395840758481, phi_seventyFourBT_87487749423608853395840758482, phi_seventyFourBT_87487749423608853395840758483,
    phi_seventyFourBT_87487749423608853395840758484, phi_seventyFourBT_87487749423608853395840758485, phi_seventyFourBT_87487749423608853395840758486,
    phi_seventyFourBT_87487749423608853395840758487, phi_seventyFourBT_87487749423608853395840758488, phi_seventyFourBT_87487749423608853395840758489,
    phi_seventyFourBT_87487749423608853395840758490, phi_seventyFourBT_87487749423608853395840758491, phi_seventyFourBT_87487749423608853395840758492,
    phi_seventyFourBT_87487749423608853395840758493, phi_seventyFourBT_87487749423608853395840758494, phi_seventyFourBT_87487749423608853395840758495,
    phi_seventyFourBT_87487749423608853395840758496, phi_seventyFourBT_87487749423608853395840758497, phi_seventyFourBT_87487749423608853395840758498,
    phi_seventyFourBT_87487749423608853395840758499, phi_seventyFourBT_87487749423608853395840758500, phi_seventyFourBT_87487749423608853395840758501]

end TotientTailPeriodKiller
end Erdos249257
