import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def eightyFiveCEFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem eightyFiveCEFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : eightyFiveCEFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [eightyFiveCEFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [eightyFiveCEFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then eightyFiveCEFastPow a n * eightyFiveCEFastPow a n * a else eightyFiveCEFastPow a n * eightyFiveCEFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_eightyFiveCE_2 : Nat.Prime 2 := by norm_num

private theorem prime_eightyFiveCE_3 : Nat.Prime 3 := by norm_num

private theorem prime_eightyFiveCE_5 : Nat.Prime 5 := by norm_num

private theorem prime_eightyFiveCE_7 : Nat.Prime 7 := by norm_num

private theorem prime_eightyFiveCE_11 : Nat.Prime 11 := by norm_num

private theorem prime_eightyFiveCE_13 : Nat.Prime 13 := by norm_num

private theorem prime_eightyFiveCE_17 : Nat.Prime 17 := by norm_num

private theorem prime_eightyFiveCE_19 : Nat.Prime 19 := by norm_num

private theorem prime_eightyFiveCE_23 : Nat.Prime 23 := by norm_num

private theorem prime_eightyFiveCE_29 : Nat.Prime 29 := by norm_num

private theorem prime_eightyFiveCE_31 : Nat.Prime 31 := by norm_num

private theorem prime_eightyFiveCE_37 : Nat.Prime 37 := by norm_num

private theorem prime_eightyFiveCE_41 : Nat.Prime 41 := by norm_num

private theorem prime_eightyFiveCE_43 : Nat.Prime 43 := by norm_num

private theorem prime_eightyFiveCE_47 : Nat.Prime 47 := by norm_num

private theorem prime_eightyFiveCE_53 : Nat.Prime 53 := by norm_num

private theorem prime_eightyFiveCE_59 : Nat.Prime 59 := by norm_num

private theorem prime_eightyFiveCE_61 : Nat.Prime 61 := by norm_num

private theorem prime_eightyFiveCE_67 : Nat.Prime 67 := by norm_num

private theorem prime_eightyFiveCE_71 : Nat.Prime 71 := by norm_num

private theorem prime_eightyFiveCE_73 : Nat.Prime 73 := by norm_num

private theorem prime_eightyFiveCE_79 : Nat.Prime 79 := by norm_num

private theorem prime_eightyFiveCE_83 : Nat.Prime 83 := by norm_num

private theorem prime_eightyFiveCE_89 : Nat.Prime 89 := by norm_num

private theorem prime_eightyFiveCE_97 : Nat.Prime 97 := by norm_num

private theorem prime_eightyFiveCE_101 : Nat.Prime 101 := by norm_num

private theorem prime_eightyFiveCE_103 : Nat.Prime 103 := by norm_num

private theorem prime_eightyFiveCE_107 : Nat.Prime 107 := by norm_num

private theorem prime_eightyFiveCE_109 : Nat.Prime 109 := by norm_num

private theorem prime_eightyFiveCE_113 : Nat.Prime 113 := by norm_num

private theorem prime_eightyFiveCE_127 : Nat.Prime 127 := by norm_num

private theorem prime_eightyFiveCE_131 : Nat.Prime 131 := by norm_num

private theorem prime_eightyFiveCE_137 : Nat.Prime 137 := by norm_num

private theorem prime_eightyFiveCE_139 : Nat.Prime 139 := by norm_num

private theorem prime_eightyFiveCE_149 : Nat.Prime 149 := by norm_num

private theorem prime_eightyFiveCE_151 : Nat.Prime 151 := by norm_num

private theorem prime_eightyFiveCE_157 : Nat.Prime 157 := by norm_num

private theorem prime_eightyFiveCE_163 : Nat.Prime 163 := by norm_num

private theorem prime_eightyFiveCE_167 : Nat.Prime 167 := by norm_num

private theorem prime_eightyFiveCE_173 : Nat.Prime 173 := by norm_num

private theorem prime_eightyFiveCE_179 : Nat.Prime 179 := by norm_num

private theorem prime_eightyFiveCE_181 : Nat.Prime 181 := by norm_num

private theorem prime_eightyFiveCE_191 : Nat.Prime 191 := by norm_num

private theorem prime_eightyFiveCE_193 : Nat.Prime 193 := by norm_num

private theorem prime_eightyFiveCE_197 : Nat.Prime 197 := by norm_num

private theorem prime_eightyFiveCE_199 : Nat.Prime 199 := by norm_num

private theorem prime_eightyFiveCE_211 : Nat.Prime 211 := by norm_num

private theorem prime_eightyFiveCE_227 : Nat.Prime 227 := by norm_num

private theorem prime_eightyFiveCE_229 : Nat.Prime 229 := by norm_num

private theorem prime_eightyFiveCE_233 : Nat.Prime 233 := by norm_num

private theorem prime_eightyFiveCE_239 : Nat.Prime 239 := by norm_num

private theorem prime_eightyFiveCE_241 : Nat.Prime 241 := by norm_num

private theorem prime_eightyFiveCE_251 : Nat.Prime 251 := by norm_num

private theorem prime_eightyFiveCE_263 : Nat.Prime 263 := by norm_num

private theorem prime_eightyFiveCE_269 : Nat.Prime 269 := by norm_num

private theorem prime_eightyFiveCE_271 : Nat.Prime 271 := by norm_num

private theorem prime_eightyFiveCE_277 : Nat.Prime 277 := by norm_num

private theorem prime_eightyFiveCE_281 : Nat.Prime 281 := by norm_num

private theorem prime_eightyFiveCE_283 : Nat.Prime 283 := by norm_num

private theorem prime_eightyFiveCE_293 : Nat.Prime 293 := by norm_num

private theorem prime_eightyFiveCE_311 : Nat.Prime 311 := by norm_num

private theorem prime_eightyFiveCE_313 : Nat.Prime 313 := by norm_num

private theorem prime_eightyFiveCE_317 : Nat.Prime 317 := by norm_num

private theorem prime_eightyFiveCE_331 : Nat.Prime 331 := by norm_num

private theorem prime_eightyFiveCE_347 : Nat.Prime 347 := by norm_num

private theorem prime_eightyFiveCE_379 : Nat.Prime 379 := by norm_num

private theorem prime_eightyFiveCE_383 : Nat.Prime 383 := by norm_num

private theorem prime_eightyFiveCE_389 : Nat.Prime 389 := by norm_num

private theorem prime_eightyFiveCE_397 : Nat.Prime 397 := by norm_num

private theorem prime_eightyFiveCE_409 : Nat.Prime 409 := by norm_num

private theorem prime_eightyFiveCE_431 : Nat.Prime 431 := by norm_num

private theorem prime_eightyFiveCE_433 : Nat.Prime 433 := by norm_num

private theorem prime_eightyFiveCE_439 : Nat.Prime 439 := by norm_num

private theorem prime_eightyFiveCE_443 : Nat.Prime 443 := by norm_num

private theorem prime_eightyFiveCE_457 : Nat.Prime 457 := by norm_num

private theorem prime_eightyFiveCE_461 : Nat.Prime 461 := by norm_num

private theorem prime_eightyFiveCE_463 : Nat.Prime 463 := by norm_num

private theorem prime_eightyFiveCE_467 : Nat.Prime 467 := by norm_num

private theorem prime_eightyFiveCE_487 : Nat.Prime 487 := by norm_num

private theorem prime_eightyFiveCE_503 : Nat.Prime 503 := by norm_num

private theorem prime_eightyFiveCE_521 : Nat.Prime 521 := by norm_num

private theorem prime_eightyFiveCE_523 : Nat.Prime 523 := by norm_num

private theorem prime_eightyFiveCE_541 : Nat.Prime 541 := by norm_num

private theorem prime_eightyFiveCE_563 : Nat.Prime 563 := by norm_num

private theorem prime_eightyFiveCE_571 : Nat.Prime 571 := by norm_num

private theorem prime_eightyFiveCE_587 : Nat.Prime 587 := by norm_num

private theorem prime_eightyFiveCE_613 : Nat.Prime 613 := by norm_num

private theorem prime_eightyFiveCE_619 : Nat.Prime 619 := by norm_num

private theorem prime_eightyFiveCE_641 : Nat.Prime 641 := by norm_num

private theorem prime_eightyFiveCE_653 : Nat.Prime 653 := by norm_num

private theorem prime_eightyFiveCE_659 : Nat.Prime 659 := by norm_num

private theorem prime_eightyFiveCE_673 : Nat.Prime 673 := by norm_num

private theorem prime_eightyFiveCE_677 : Nat.Prime 677 := by norm_num

private theorem prime_eightyFiveCE_683 : Nat.Prime 683 := by norm_num

private theorem prime_eightyFiveCE_691 : Nat.Prime 691 := by norm_num

private theorem prime_eightyFiveCE_701 : Nat.Prime 701 := by norm_num

private theorem prime_eightyFiveCE_709 : Nat.Prime 709 := by norm_num

private theorem prime_eightyFiveCE_761 : Nat.Prime 761 := by norm_num

private theorem prime_eightyFiveCE_787 : Nat.Prime 787 := by norm_num

private theorem prime_eightyFiveCE_797 : Nat.Prime 797 := by norm_num

private theorem prime_eightyFiveCE_839 : Nat.Prime 839 := by norm_num

private theorem prime_eightyFiveCE_877 : Nat.Prime 877 := by norm_num

private theorem prime_eightyFiveCE_937 : Nat.Prime 937 := by norm_num

private theorem prime_eightyFiveCE_947 : Nat.Prime 947 := by norm_num

private theorem prime_eightyFiveCE_983 : Nat.Prime 983 := by norm_num

private theorem prime_eightyFiveCE_997 : Nat.Prime 997 := by norm_num

private theorem prime_eightyFiveCE_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_eightyFiveCE_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_eightyFiveCE_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_eightyFiveCE_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_eightyFiveCE_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_eightyFiveCE_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_eightyFiveCE_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_eightyFiveCE_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_eightyFiveCE_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_eightyFiveCE_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_eightyFiveCE_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_eightyFiveCE_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_eightyFiveCE_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_eightyFiveCE_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_eightyFiveCE_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_eightyFiveCE_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_eightyFiveCE_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_eightyFiveCE_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_eightyFiveCE_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_eightyFiveCE_1439 : Nat.Prime 1439 := by norm_num

private theorem prime_eightyFiveCE_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_eightyFiveCE_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_eightyFiveCE_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_eightyFiveCE_1613 : Nat.Prime 1613 := by norm_num

private theorem prime_eightyFiveCE_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_eightyFiveCE_1759 : Nat.Prime 1759 := by norm_num

private theorem prime_eightyFiveCE_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_eightyFiveCE_1871 : Nat.Prime 1871 := by norm_num

private theorem prime_eightyFiveCE_1931 : Nat.Prime 1931 := by norm_num

private theorem prime_eightyFiveCE_1949 : Nat.Prime 1949 := by norm_num

private theorem prime_eightyFiveCE_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_eightyFiveCE_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_eightyFiveCE_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_eightyFiveCE_2027 : Nat.Prime 2027 := by norm_num

private theorem prime_eightyFiveCE_2141 : Nat.Prime 2141 := by norm_num

private theorem prime_eightyFiveCE_2207 : Nat.Prime 2207 := by norm_num

private theorem prime_eightyFiveCE_2221 : Nat.Prime 2221 := by norm_num

private theorem prime_eightyFiveCE_2383 : Nat.Prime 2383 := by norm_num

private theorem prime_eightyFiveCE_2447 : Nat.Prime 2447 := by norm_num

private theorem prime_eightyFiveCE_2551 : Nat.Prime 2551 := by norm_num

private theorem prime_eightyFiveCE_2609 : Nat.Prime 2609 := by norm_num

private theorem prime_eightyFiveCE_2707 : Nat.Prime 2707 := by norm_num

private theorem prime_eightyFiveCE_2729 : Nat.Prime 2729 := by norm_num

private theorem prime_eightyFiveCE_2803 : Nat.Prime 2803 := by norm_num

private theorem prime_eightyFiveCE_2833 : Nat.Prime 2833 := by norm_num

private theorem prime_eightyFiveCE_2843 : Nat.Prime 2843 := by norm_num

private theorem prime_eightyFiveCE_2917 : Nat.Prime 2917 := by norm_num

private theorem prime_eightyFiveCE_2963 : Nat.Prime 2963 := by norm_num

private theorem prime_eightyFiveCE_3257 : Nat.Prime 3257 := by norm_num

private theorem prime_eightyFiveCE_3259 : Nat.Prime 3259 := by norm_num

private theorem prime_eightyFiveCE_3323 : Nat.Prime 3323 := by norm_num

private theorem prime_eightyFiveCE_3557 : Nat.Prime 3557 := by norm_num

private theorem prime_eightyFiveCE_3677 : Nat.Prime 3677 := by norm_num

private theorem prime_eightyFiveCE_3709 : Nat.Prime 3709 := by norm_num

private theorem prime_eightyFiveCE_3719 : Nat.Prime 3719 := by norm_num

private theorem prime_eightyFiveCE_3733 : Nat.Prime 3733 := by norm_num

private theorem prime_eightyFiveCE_3739 : Nat.Prime 3739 := by norm_num

private theorem prime_eightyFiveCE_3823 : Nat.Prime 3823 := by norm_num

private theorem prime_eightyFiveCE_3943 : Nat.Prime 3943 := by norm_num

private theorem prime_eightyFiveCE_4127 : Nat.Prime 4127 := by norm_num

private theorem prime_eightyFiveCE_4139 : Nat.Prime 4139 := by norm_num

private theorem prime_eightyFiveCE_4273 : Nat.Prime 4273 := by norm_num

private theorem prime_eightyFiveCE_4621 : Nat.Prime 4621 := by norm_num

private theorem prime_eightyFiveCE_4673 : Nat.Prime 4673 := by norm_num

private theorem prime_eightyFiveCE_4801 : Nat.Prime 4801 := by norm_num

private theorem prime_eightyFiveCE_4813 : Nat.Prime 4813 := by norm_num

private theorem prime_eightyFiveCE_5081 : Nat.Prime 5081 := by norm_num

private theorem prime_eightyFiveCE_5237 : Nat.Prime 5237 := by norm_num

private theorem prime_eightyFiveCE_5323 : Nat.Prime 5323 := by norm_num

private theorem prime_eightyFiveCE_5623 : Nat.Prime 5623 := by norm_num

private theorem prime_eightyFiveCE_5743 : Nat.Prime 5743 := by norm_num

private theorem prime_eightyFiveCE_5867 : Nat.Prime 5867 := by norm_num

private theorem prime_eightyFiveCE_6143 : Nat.Prime 6143 := by norm_num

private theorem prime_eightyFiveCE_6217 : Nat.Prime 6217 := by norm_num

private theorem prime_eightyFiveCE_6367 : Nat.Prime 6367 := by norm_num

private theorem prime_eightyFiveCE_6389 : Nat.Prime 6389 := by norm_num

private theorem prime_eightyFiveCE_6397 : Nat.Prime 6397 := by norm_num

private theorem prime_eightyFiveCE_6521 : Nat.Prime 6521 := by norm_num

private theorem prime_eightyFiveCE_6689 : Nat.Prime 6689 := by norm_num

private theorem prime_eightyFiveCE_6719 : Nat.Prime 6719 := by norm_num

private theorem prime_eightyFiveCE_6907 : Nat.Prime 6907 := by norm_num

private theorem prime_eightyFiveCE_7121 : Nat.Prime 7121 := by norm_num

private theorem prime_eightyFiveCE_7151 : Nat.Prime 7151 := by norm_num

private theorem prime_eightyFiveCE_7243 : Nat.Prime 7243 := by norm_num

private theorem prime_eightyFiveCE_7451 : Nat.Prime 7451 := by norm_num

private theorem prime_eightyFiveCE_7487 : Nat.Prime 7487 := by norm_num

private theorem prime_eightyFiveCE_7489 : Nat.Prime 7489 := by norm_num

private theorem prime_eightyFiveCE_7499 : Nat.Prime 7499 := by norm_num

private theorem prime_eightyFiveCE_7789 : Nat.Prime 7789 := by norm_num

private theorem prime_eightyFiveCE_8011 : Nat.Prime 8011 := by norm_num

private theorem prime_eightyFiveCE_8087 : Nat.Prime 8087 := by norm_num

private theorem prime_eightyFiveCE_8093 : Nat.Prime 8093 := by norm_num

private theorem prime_eightyFiveCE_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_eightyFiveCE_8563 : Nat.Prime 8563 := by norm_num

private theorem prime_eightyFiveCE_8677 : Nat.Prime 8677 := by norm_num

private theorem prime_eightyFiveCE_8681 : Nat.Prime 8681 := by norm_num

private theorem prime_eightyFiveCE_8819 : Nat.Prime 8819 := by norm_num

private theorem prime_eightyFiveCE_9631 : Nat.Prime 9631 := by norm_num

private theorem prime_eightyFiveCE_9679 : Nat.Prime 9679 := by norm_num

private theorem prime_eightyFiveCE_9721 : Nat.Prime 9721 := by norm_num

private theorem prime_eightyFiveCE_10457 : Nat.Prime 10457 := by norm_num

private theorem prime_eightyFiveCE_10501 : Nat.Prime 10501 := by norm_num

private theorem prime_eightyFiveCE_10883 : Nat.Prime 10883 := by norm_num

private theorem prime_eightyFiveCE_10987 : Nat.Prime 10987 := by norm_num

private theorem prime_eightyFiveCE_11213 : Nat.Prime 11213 := by norm_num

private theorem prime_eightyFiveCE_11411 : Nat.Prime 11411 := by norm_num

private theorem prime_eightyFiveCE_11813 : Nat.Prime 11813 := by norm_num

private theorem prime_eightyFiveCE_12097 : Nat.Prime 12097 := by norm_num

private theorem prime_eightyFiveCE_12113 : Nat.Prime 12113 := by norm_num

private theorem prime_eightyFiveCE_12401 : Nat.Prime 12401 := by norm_num

private theorem prime_eightyFiveCE_12659 : Nat.Prime 12659 := by norm_num

private theorem prime_eightyFiveCE_13093 : Nat.Prime 13093 := by norm_num

private theorem prime_eightyFiveCE_13291 : Nat.Prime 13291 := by norm_num

private theorem prime_eightyFiveCE_13337 : Nat.Prime 13337 := by norm_num

private theorem prime_eightyFiveCE_13339 : Nat.Prime 13339 := by norm_num

private theorem prime_eightyFiveCE_13451 : Nat.Prime 13451 := by norm_num

private theorem prime_eightyFiveCE_13499 : Nat.Prime 13499 := by norm_num

private theorem prime_eightyFiveCE_13799 : Nat.Prime 13799 := by norm_num

private theorem prime_eightyFiveCE_13831 : Nat.Prime 13831 := by norm_num

private theorem prime_eightyFiveCE_13873 : Nat.Prime 13873 := by norm_num

private theorem prime_eightyFiveCE_14081 : Nat.Prime 14081 := by norm_num

private theorem prime_eightyFiveCE_14723 : Nat.Prime 14723 := by norm_num

private theorem prime_eightyFiveCE_14929 : Nat.Prime 14929 := by norm_num

private theorem prime_eightyFiveCE_15401 : Nat.Prime 15401 := by norm_num

private theorem prime_eightyFiveCE_16073 : Nat.Prime 16073 := by norm_num

private theorem prime_eightyFiveCE_16433 : Nat.Prime 16433 := by norm_num

private theorem prime_eightyFiveCE_16493 : Nat.Prime 16493 := by norm_num

private theorem prime_eightyFiveCE_18127 : Nat.Prime 18127 := by norm_num

private theorem prime_eightyFiveCE_19051 : Nat.Prime 19051 := by norm_num

private theorem prime_eightyFiveCE_19183 : Nat.Prime 19183 := by norm_num

private theorem prime_eightyFiveCE_19861 : Nat.Prime 19861 := by norm_num

private theorem prime_eightyFiveCE_20399 : Nat.Prime 20399 := by norm_num

private theorem prime_eightyFiveCE_20983 : Nat.Prime 20983 := by norm_num

private theorem prime_eightyFiveCE_21493 : Nat.Prime 21493 := by norm_num

private theorem prime_eightyFiveCE_22247 : Nat.Prime 22247 := by norm_num

private theorem prime_eightyFiveCE_23173 : Nat.Prime 23173 := by norm_num

private theorem prime_eightyFiveCE_23473 : Nat.Prime 23473 := by norm_num

private theorem prime_eightyFiveCE_23819 : Nat.Prime 23819 := by norm_num

private theorem prime_eightyFiveCE_23917 : Nat.Prime 23917 := by norm_num

private theorem prime_eightyFiveCE_24077 : Nat.Prime 24077 := by norm_num

private theorem prime_eightyFiveCE_25583 : Nat.Prime 25583 := by norm_num

private theorem prime_eightyFiveCE_25747 : Nat.Prime 25747 := by norm_num

private theorem prime_eightyFiveCE_25969 : Nat.Prime 25969 := by norm_num

private theorem prime_eightyFiveCE_26927 : Nat.Prime 26927 := by norm_num

private theorem prime_eightyFiveCE_27481 : Nat.Prime 27481 := by norm_num

private theorem prime_eightyFiveCE_28463 : Nat.Prime 28463 := by norm_num

private theorem prime_eightyFiveCE_28813 : Nat.Prime 28813 := by norm_num

private theorem prime_eightyFiveCE_32369 : Nat.Prime 32369 := by norm_num

private theorem prime_eightyFiveCE_33211 : Nat.Prime 33211 := by norm_num

private theorem prime_eightyFiveCE_35149 : Nat.Prime 35149 := by norm_num

private theorem prime_eightyFiveCE_36457 : Nat.Prime 36457 := by norm_num

private theorem prime_eightyFiveCE_37783 : Nat.Prime 37783 := by norm_num

private theorem prime_eightyFiveCE_39359 : Nat.Prime 39359 := by norm_num

private theorem prime_eightyFiveCE_40531 : Nat.Prime 40531 := by norm_num

private theorem prime_eightyFiveCE_41543 : Nat.Prime 41543 := by norm_num

private theorem prime_eightyFiveCE_42139 : Nat.Prime 42139 := by norm_num

private theorem prime_eightyFiveCE_43117 : Nat.Prime 43117 := by norm_num

private theorem prime_eightyFiveCE_43451 : Nat.Prime 43451 := by norm_num

private theorem prime_eightyFiveCE_45389 : Nat.Prime 45389 := by norm_num

private theorem prime_eightyFiveCE_46769 : Nat.Prime 46769 := by norm_num

private theorem prime_eightyFiveCE_48409 : Nat.Prime 48409 := by norm_num

private theorem prime_eightyFiveCE_48619 : Nat.Prime 48619 := by norm_num

private theorem prime_eightyFiveCE_50159 : Nat.Prime 50159 := by norm_num

private theorem prime_eightyFiveCE_52579 : Nat.Prime 52579 := by norm_num

private theorem prime_eightyFiveCE_53783 : Nat.Prime 53783 := by norm_num

private theorem prime_eightyFiveCE_54667 : Nat.Prime 54667 := by norm_num

private theorem prime_eightyFiveCE_60353 : Nat.Prime 60353 := by norm_num

private theorem prime_eightyFiveCE_64333 : Nat.Prime 64333 := by norm_num

private theorem prime_eightyFiveCE_66959 : Nat.Prime 66959 := by norm_num

private theorem prime_eightyFiveCE_68311 : Nat.Prime 68311 := by norm_num

private theorem prime_eightyFiveCE_71359 : Nat.Prime 71359 := by norm_num

private theorem prime_eightyFiveCE_72101 : Nat.Prime 72101 := by norm_num

private theorem prime_eightyFiveCE_73709 : Nat.Prime 73709 := by norm_num

private theorem prime_eightyFiveCE_75743 : Nat.Prime 75743 := by norm_num

private theorem prime_eightyFiveCE_76253 : Nat.Prime 76253 := by norm_num

private theorem prime_eightyFiveCE_78697 : Nat.Prime 78697 := by norm_num

private theorem prime_eightyFiveCE_85133 : Nat.Prime 85133 := by norm_num

private theorem prime_eightyFiveCE_85369 : Nat.Prime 85369 := by norm_num

private theorem prime_eightyFiveCE_89213 : Nat.Prime 89213 := by norm_num

private theorem prime_eightyFiveCE_89387 : Nat.Prime 89387 := by norm_num

private theorem prime_eightyFiveCE_91229 : Nat.Prime 91229 := by norm_num

private theorem prime_eightyFiveCE_94789 : Nat.Prime 94789 := by norm_num

private theorem prime_eightyFiveCE_97553 : Nat.Prime 97553 := by norm_num

private theorem prime_eightyFiveCE_98909 : Nat.Prime 98909 := by norm_num

private theorem prime_eightyFiveCE_107693 : Nat.Prime 107693 := by norm_num

private theorem prime_eightyFiveCE_111773 : Nat.Prime 111773 := by norm_num

private theorem prime_eightyFiveCE_117427 : Nat.Prime 117427 := by norm_num

private theorem prime_eightyFiveCE_121019 : Nat.Prime 121019 := by norm_num

private theorem prime_eightyFiveCE_124067 : Nat.Prime 124067 := by norm_num

private theorem prime_eightyFiveCE_131213 : Nat.Prime 131213 := by norm_num

private theorem prime_eightyFiveCE_134731 : Nat.Prime 134731 := by norm_num

private theorem prime_eightyFiveCE_136601 : Nat.Prime 136601 := by norm_num

private theorem prime_eightyFiveCE_139861 : Nat.Prime 139861 := by norm_num

private theorem prime_eightyFiveCE_145661 : Nat.Prime 145661 := by norm_num

private theorem prime_eightyFiveCE_148207 : Nat.Prime 148207 := by norm_num

private theorem prime_eightyFiveCE_149921 : Nat.Prime 149921 := by norm_num

private theorem prime_eightyFiveCE_156019 : Nat.Prime 156019 := by norm_num

private theorem prime_eightyFiveCE_157411 : Nat.Prime 157411 := by norm_num

private theorem prime_eightyFiveCE_162751 : Nat.Prime 162751 := by norm_num

private theorem prime_eightyFiveCE_165247 : Nat.Prime 165247 := by norm_num

private theorem prime_eightyFiveCE_175067 : Nat.Prime 175067 := by norm_num

private theorem prime_eightyFiveCE_178417 : Nat.Prime 178417 := by norm_num

private theorem prime_eightyFiveCE_196081 : Nat.Prime 196081 := by norm_num

private theorem prime_eightyFiveCE_199889 : Nat.Prime 199889 := by norm_num

private theorem prime_eightyFiveCE_225977 : Nat.Prime 225977 := by norm_num

private theorem prime_eightyFiveCE_228733 : Nat.Prime 228733 := by norm_num

private theorem prime_eightyFiveCE_231347 : Nat.Prime 231347 := by norm_num

private theorem prime_eightyFiveCE_240829 : Nat.Prime 240829 := by norm_num

private theorem prime_eightyFiveCE_243671 : Nat.Prime 243671 := by norm_num

private theorem prime_eightyFiveCE_248749 : Nat.Prime 248749 := by norm_num

private theorem prime_eightyFiveCE_268607 : Nat.Prime 268607 := by norm_num

private theorem prime_eightyFiveCE_271273 : Nat.Prime 271273 := by norm_num

private theorem prime_eightyFiveCE_274529 : Nat.Prime 274529 := by norm_num

private theorem prime_eightyFiveCE_310223 : Nat.Prime 310223 := by norm_num

private theorem prime_eightyFiveCE_348527 : Nat.Prime 348527 := by norm_num

private theorem prime_eightyFiveCE_360307 : Nat.Prime 360307 := by norm_num

private theorem prime_eightyFiveCE_368107 : Nat.Prime 368107 := by norm_num

private theorem prime_eightyFiveCE_370891 : Nat.Prime 370891 := by norm_num

private theorem prime_eightyFiveCE_377843 : Nat.Prime 377843 := by norm_num

private theorem prime_eightyFiveCE_381037 : Nat.Prime 381037 := by norm_num

private theorem prime_eightyFiveCE_393103 : Nat.Prime 393103 := by norm_num

private theorem prime_eightyFiveCE_413141 : Nat.Prime 413141 := by norm_num

private theorem prime_eightyFiveCE_425027 : Nat.Prime 425027 := by norm_num

private theorem prime_eightyFiveCE_429007 : Nat.Prime 429007 := by norm_num

private theorem prime_eightyFiveCE_441011 : Nat.Prime 441011 := by norm_num

private theorem prime_eightyFiveCE_442879 : Nat.Prime 442879 := by norm_num

private theorem prime_eightyFiveCE_477811 : Nat.Prime 477811 := by norm_num

private theorem prime_eightyFiveCE_508619 : Nat.Prime 508619 := by norm_num

private theorem prime_eightyFiveCE_517081 : Nat.Prime 517081 := by norm_num

private theorem prime_eightyFiveCE_519703 : Nat.Prime 519703 := by norm_num

private theorem prime_eightyFiveCE_544373 : Nat.Prime 544373 := by norm_num

private theorem prime_eightyFiveCE_579563 : Nat.Prime 579563 := by norm_num

private theorem prime_eightyFiveCE_582859 : Nat.Prime 582859 := by norm_num

private theorem prime_eightyFiveCE_593851 : Nat.Prime 593851 := by norm_num

private theorem prime_eightyFiveCE_643213 : Nat.Prime 643213 := by norm_num

private theorem prime_eightyFiveCE_654067 : Nat.Prime 654067 := by norm_num

private theorem prime_eightyFiveCE_655643 : Nat.Prime 655643 := by norm_num

private theorem prime_eightyFiveCE_669433 : Nat.Prime 669433 := by norm_num

private theorem prime_eightyFiveCE_669869 : Nat.Prime 669869 := by norm_num

private theorem prime_eightyFiveCE_741721 : Nat.Prime 741721 := by norm_num

private theorem prime_eightyFiveCE_760423 : Nat.Prime 760423 := by norm_num

private theorem prime_eightyFiveCE_788873 : Nat.Prime 788873 := by norm_num

private theorem prime_eightyFiveCE_795097 : Nat.Prime 795097 := by norm_num

private theorem prime_eightyFiveCE_808229 : Nat.Prime 808229 := by norm_num

private theorem prime_eightyFiveCE_889879 : Nat.Prime 889879 := by norm_num

private theorem prime_eightyFiveCE_916907 : Nat.Prime 916907 := by norm_num

private theorem prime_eightyFiveCE_1003019 : Nat.Prime 1003019 := by norm_num

private theorem prime_eightyFiveCE_1041701 : Nat.Prime 1041701 := by norm_num

private theorem prime_eightyFiveCE_1079339 : Nat.Prime 1079339 := by norm_num

private theorem prime_eightyFiveCE_1165001 : Nat.Prime 1165001 := by norm_num

private theorem prime_eightyFiveCE_1170311 : Nat.Prime 1170311 := by norm_num

private theorem prime_eightyFiveCE_1175659 : Nat.Prime 1175659 := by norm_num

private theorem prime_eightyFiveCE_1200371 : Nat.Prime 1200371 := by norm_num

private theorem prime_eightyFiveCE_1206539 : Nat.Prime 1206539 := by norm_num

private theorem prime_eightyFiveCE_1224169 : Nat.Prime 1224169 := by norm_num

private theorem prime_eightyFiveCE_1266899 : Nat.Prime 1266899 := by norm_num

private theorem prime_eightyFiveCE_1276861 : Nat.Prime 1276861 := by norm_num

private theorem prime_eightyFiveCE_1334239 : Nat.Prime 1334239 := by norm_num

private theorem prime_eightyFiveCE_1366753 : Nat.Prime 1366753 := by norm_num

private theorem prime_eightyFiveCE_1424531 : Nat.Prime 1424531 := by norm_num

private theorem prime_eightyFiveCE_1477643 : Nat.Prime 1477643 := by norm_num

private theorem prime_eightyFiveCE_1523563 : Nat.Prime 1523563 := by norm_num

private theorem prime_eightyFiveCE_1534549 : Nat.Prime 1534549 := by norm_num

private theorem prime_eightyFiveCE_1594933 : Nat.Prime 1594933 := by norm_num

private theorem prime_eightyFiveCE_1636049 : Nat.Prime 1636049 := by norm_num

private theorem prime_eightyFiveCE_1726447 : Nat.Prime 1726447 := by norm_num

private theorem prime_eightyFiveCE_1860533 : Nat.Prime 1860533 := by norm_num

private theorem prime_eightyFiveCE_1916839 : Nat.Prime 1916839 := by norm_num

private theorem prime_eightyFiveCE_1956611 : Nat.Prime 1956611 := by norm_num

private theorem prime_eightyFiveCE_2049667 : Nat.Prime 2049667 := by norm_num

private theorem prime_eightyFiveCE_2110477 : Nat.Prime 2110477 := by norm_num

private theorem prime_eightyFiveCE_2177531 : Nat.Prime 2177531 := by norm_num

private theorem prime_eightyFiveCE_2220971 : Nat.Prime 2220971 := by norm_num

private theorem prime_eightyFiveCE_2305487 : Nat.Prime 2305487 := by norm_num

private theorem prime_eightyFiveCE_2330681 : Nat.Prime 2330681 := by norm_num

private theorem prime_eightyFiveCE_2412959 : Nat.Prime 2412959 := by norm_num

private theorem prime_eightyFiveCE_2725433 : Nat.Prime 2725433 := by norm_num

private theorem prime_eightyFiveCE_2784239 : Nat.Prime 2784239 := by norm_num

private theorem prime_eightyFiveCE_2851403 : Nat.Prime 2851403 := by norm_num

private theorem prime_eightyFiveCE_2958947 : Nat.Prime 2958947 := by norm_num

private theorem prime_eightyFiveCE_3131221 : Nat.Prime 3131221 := by norm_num

private theorem prime_eightyFiveCE_3350383 : Nat.Prime 3350383 := by norm_num

private theorem prime_eightyFiveCE_3495397 : Nat.Prime 3495397 := by norm_num

private theorem prime_eightyFiveCE_3848657 : Nat.Prime 3848657 := by norm_num

private theorem prime_eightyFiveCE_3960497 : Nat.Prime 3960497 := by norm_num

private theorem prime_eightyFiveCE_3971587 : Nat.Prime 3971587 := by norm_num

private theorem prime_eightyFiveCE_4005433 : Nat.Prime 4005433 := by norm_num

private theorem prime_eightyFiveCE_4428383 : Nat.Prime 4428383 := by norm_num

private theorem prime_eightyFiveCE_5036453 : Nat.Prime 5036453 := by norm_num

private theorem prime_eightyFiveCE_5115863 : Nat.Prime 5115863 := by norm_num

private theorem prime_eightyFiveCE_5126221 : Nat.Prime 5126221 := by norm_num

private theorem prime_eightyFiveCE_5207003 : Nat.Prime 5207003 := by norm_num

private theorem prime_eightyFiveCE_5383459 : Nat.Prime 5383459 := by norm_num

private theorem prime_eightyFiveCE_5475199 : Nat.Prime 5475199 := by norm_num

private theorem prime_eightyFiveCE_6313129 : Nat.Prime 6313129 := by norm_num

private theorem prime_eightyFiveCE_6661553 : Nat.Prime 6661553 := by norm_num

private theorem prime_eightyFiveCE_7313749 : Nat.Prime 7313749 := by norm_num

private theorem prime_eightyFiveCE_7407539 : Nat.Prime 7407539 := by norm_num

private theorem prime_eightyFiveCE_8240143 : Nat.Prime 8240143 := by norm_num

private theorem prime_eightyFiveCE_8308579 : Nat.Prime 8308579 := by norm_num

private theorem prime_eightyFiveCE_8452307 : Nat.Prime 8452307 := by norm_num

private theorem prime_eightyFiveCE_8602817 : Nat.Prime 8602817 := by norm_num

private theorem prime_eightyFiveCE_9117827 : Nat.Prime 9117827 := by norm_num

private theorem prime_eightyFiveCE_9958709 : Nat.Prime 9958709 := by norm_num

private theorem prime_eightyFiveCE_10228643 : Nat.Prime 10228643 := by norm_num

private theorem prime_eightyFiveCE_10461611 : Nat.Prime 10461611 := by norm_num

private theorem prime_eightyFiveCE_11030687 : Nat.Prime 11030687 := by norm_num

private theorem prime_eightyFiveCE_11245043 : Nat.Prime 11245043 := by norm_num

private theorem prime_eightyFiveCE_11371057 : Nat.Prime 11371057 := by norm_num

private theorem prime_eightyFiveCE_13217311 : Nat.Prime 13217311 := by norm_num

private theorem prime_eightyFiveCE_14674963 : Nat.Prime 14674963 := by norm_num

private theorem prime_eightyFiveCE_15245729 : Nat.Prime 15245729 := by norm_num

private theorem prime_eightyFiveCE_16403561 : Nat.Prime 16403561 := by norm_num

private theorem prime_eightyFiveCE_16727987 : Nat.Prime 16727987 := by norm_num

private theorem prime_eightyFiveCE_17216671 : Nat.Prime 17216671 := by norm_num

private theorem prime_eightyFiveCE_18383411 : Nat.Prime 18383411 := by norm_num

private theorem prime_eightyFiveCE_19924277 : Nat.Prime 19924277 := by norm_num

private theorem prime_eightyFiveCE_20334163 : Nat.Prime 20334163 := by norm_num

private theorem prime_eightyFiveCE_20910521 : Nat.Prime 20910521 := by norm_num

private theorem prime_eightyFiveCE_22618171 : Nat.Prime 22618171 := by norm_num

private theorem prime_eightyFiveCE_23385289 : Nat.Prime 23385289 := by norm_num

private theorem prime_eightyFiveCE_23502053 : Nat.Prime 23502053 := by norm_num

private theorem prime_eightyFiveCE_23526311 : Nat.Prime 23526311 := by norm_num

private theorem prime_eightyFiveCE_23561143 : Nat.Prime 23561143 := by norm_num

private theorem prime_eightyFiveCE_23684041 : Nat.Prime 23684041 := by norm_num

private theorem prime_eightyFiveCE_23700587 : Nat.Prime 23700587 := by norm_num

private theorem prime_eightyFiveCE_23859811 : Nat.Prime 23859811 := by norm_num

private theorem prime_eightyFiveCE_24237449 : Nat.Prime 24237449 := by norm_num

private theorem prime_eightyFiveCE_25176527 : Nat.Prime 25176527 := by norm_num

private theorem prime_eightyFiveCE_28288751 : Nat.Prime 28288751 := by norm_num

private theorem prime_eightyFiveCE_29932489 : Nat.Prime 29932489 := by norm_num

private theorem prime_eightyFiveCE_31558433 : Nat.Prime 31558433 := by
  apply lucas_primality 31558433 (3 : ZMod 31558433)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (47, 1), (20983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (47, 1), (20983, 1)] : List FactorBlock).map factorBlockValue).prod) = 31558433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_47
      · exact prime_eightyFiveCE_20983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 31558433) ^ 15779216 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 31558433) ^ 671456 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 31558433) ^ 1504 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_32155639 : Nat.Prime 32155639 := by
  apply lucas_primality 32155639 (3 : ZMod 32155639)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (127, 1), (2221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (127, 1), (2221, 1)] : List FactorBlock).map factorBlockValue).prod) = 32155639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_127
      · exact prime_eightyFiveCE_2221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32155639) ^ 16077819 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 32155639) ^ 10718546 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 32155639) ^ 1692402 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 32155639) ^ 253194 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 32155639) ^ 14478 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_34534271 : Nat.Prime 34534271 := by
  apply lucas_primality 34534271 (7 : ZMod 34534271)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (53, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (53, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod) = 34534271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_23
      · exact prime_eightyFiveCE_53
      · exact prime_eightyFiveCE_2833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 34534271) ^ 17267135 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 34534271) ^ 6906854 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 34534271) ^ 1501490 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 34534271) ^ 651590 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 34534271) ^ 12190 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_34589473 : Nat.Prime 34589473 := by
  apply lucas_primality 34589473 (10 : ZMod 34589473)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (360307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (360307, 1)] : List FactorBlock).map factorBlockValue).prod) = 34589473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_360307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 34589473) ^ 17294736 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 34589473) ^ 11529824 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 34589473) ^ 96 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_37110737 : Nat.Prime 37110737 := by
  apply lucas_primality 37110737 (3 : ZMod 37110737)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (178417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (178417, 1)] : List FactorBlock).map factorBlockValue).prod) = 37110737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_178417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 37110737) ^ 18555368 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 37110737) ^ 2854672 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 37110737) ^ 208 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_41090603 : Nat.Prime 41090603 := by
  apply lucas_primality 41090603 (2 : ZMod 41090603)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (109, 1), (26927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (109, 1), (26927, 1)] : List FactorBlock).map factorBlockValue).prod) = 41090603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_109
      · exact prime_eightyFiveCE_26927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41090603) ^ 20545301 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41090603) ^ 5870086 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41090603) ^ 376978 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41090603) ^ 1526 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_41842607 : Nat.Prime 41842607 := by
  apply lucas_primality 41842607 (5 : ZMod 41842607)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (233, 1), (6907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (233, 1), (6907, 1)] : List FactorBlock).map factorBlockValue).prod) = 41842607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_233
      · exact prime_eightyFiveCE_6907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 41842607) ^ 20921303 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 41842607) ^ 3218662 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 41842607) ^ 179582 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 41842607) ^ 6058 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_43824247 : Nat.Prime 43824247 := by
  apply lucas_primality 43824247 (5 : ZMod 43824247)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (541, 1), (587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (541, 1), (587, 1)] : List FactorBlock).map factorBlockValue).prod) = 43824247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_23
      · exact prime_eightyFiveCE_541
      · exact prime_eightyFiveCE_587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 43824247) ^ 21912123 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 43824247) ^ 14608082 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 43824247) ^ 1905402 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 43824247) ^ 81006 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 43824247) ^ 74658 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_44963297 : Nat.Prime 44963297 := by
  apply lucas_primality 44963297 (3 : ZMod 44963297)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (181, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (181, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 44963297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_181
      · exact prime_eightyFiveCE_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 44963297) ^ 22481648 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 44963297) ^ 6423328 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 44963297) ^ 248416 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 44963297) ^ 40544 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_46860311 : Nat.Prime 46860311 := by
  apply lucas_primality 46860311 (7 : ZMod 46860311)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (669433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (669433, 1)] : List FactorBlock).map factorBlockValue).prod) = 46860311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_669433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 46860311) ^ 23430155 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 46860311) ^ 9372062 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 46860311) ^ 6694330 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 46860311) ^ 70 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_47197411 : Nat.Prime 47197411 := by
  apply lucas_primality 47197411 (3 : ZMod 47197411)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (121019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (121019, 1)] : List FactorBlock).map factorBlockValue).prod) = 47197411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_121019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 47197411) ^ 23598705 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 47197411) ^ 15732470 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 47197411) ^ 9439482 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 47197411) ^ 3630570 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 47197411) ^ 390 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_54093997 : Nat.Prime 54093997 := by
  apply lucas_primality 54093997 (2 : ZMod 54093997)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (136601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (136601, 1)] : List FactorBlock).map factorBlockValue).prod) = 54093997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_136601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 54093997) ^ 27046998 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 54093997) ^ 18031332 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 54093997) ^ 4917636 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 54093997) ^ 396 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_54315421 : Nat.Prime 54315421 := by
  apply lucas_primality 54315421 (7 : ZMod 54315421)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (23, 1), (39359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (23, 1), (39359, 1)] : List FactorBlock).map factorBlockValue).prod) = 54315421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_23
      · exact prime_eightyFiveCE_39359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 54315421) ^ 27157710 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 54315421) ^ 18105140 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 54315421) ^ 10863084 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 54315421) ^ 2361540 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 54315421) ^ 1380 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_57403627 : Nat.Prime 57403627 := by
  apply lucas_primality 57403627 (5 : ZMod 57403627)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1366753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1366753, 1)] : List FactorBlock).map factorBlockValue).prod) = 57403627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_1366753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 57403627) ^ 28701813 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 57403627) ^ 19134542 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 57403627) ^ 8200518 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 57403627) ^ 42 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_63040381 : Nat.Prime 63040381 := by
  apply lucas_primality 63040381 (2 : ZMod 63040381)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 2), (6217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 2), (6217, 1)] : List FactorBlock).map factorBlockValue).prod) = 63040381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_6217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 63040381) ^ 31520190 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 63040381) ^ 21013460 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 63040381) ^ 12608076 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 63040381) ^ 4849260 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 63040381) ^ 10140 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_65600401 : Nat.Prime 65600401 := by
  apply lucas_primality 65600401 (14 : ZMod 65600401)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (54667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (54667, 1)] : List FactorBlock).map factorBlockValue).prod) = 65600401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_54667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 65600401) ^ 32800200 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 65600401) ^ 21866800 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 65600401) ^ 13120080 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 65600401) ^ 1200 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_66773351 : Nat.Prime 66773351 := by
  apply lucas_primality 66773351 (7 : ZMod 66773351)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (107, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (107, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) = 66773351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_107
      · exact prime_eightyFiveCE_1783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 66773351) ^ 33386675 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 66773351) ^ 13354670 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 66773351) ^ 9539050 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 66773351) ^ 624050 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 66773351) ^ 37450 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_67202341 : Nat.Prime 67202341 := by
  apply lucas_primality 67202341 (2 : ZMod 67202341)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (67, 1), (73, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (67, 1), (73, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod) = 67202341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_67
      · exact prime_eightyFiveCE_73
      · exact prime_eightyFiveCE_229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 67202341) ^ 33601170 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 67202341) ^ 22400780 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 67202341) ^ 13440468 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 67202341) ^ 1003020 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 67202341) ^ 920580 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 67202341) ^ 293460 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_76046587 : Nat.Prime 76046587 := by
  apply lucas_primality 76046587 (2 : ZMod 76046587)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (241, 1), (683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (241, 1), (683, 1)] : List FactorBlock).map factorBlockValue).prod) = 76046587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_241
      · exact prime_eightyFiveCE_683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 76046587) ^ 38023293 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 76046587) ^ 25348862 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 76046587) ^ 10863798 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 76046587) ^ 6913326 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 76046587) ^ 315546 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 76046587) ^ 111342 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_79303867 : Nat.Prime 79303867 := by
  apply lucas_primality 79303867 (2 : ZMod 79303867)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13217311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13217311, 1)] : List FactorBlock).map factorBlockValue).prod) = 79303867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_13217311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 79303867) ^ 39651933 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 79303867) ^ 26434622 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 79303867) ^ 6 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_82181207 : Nat.Prime 82181207 := by
  apply lucas_primality 82181207 (5 : ZMod 82181207)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41090603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41090603, 1)] : List FactorBlock).map factorBlockValue).prod) = 82181207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_41090603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 82181207) ^ 41090603 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 82181207) ^ 2 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_86937089 : Nat.Prime 86937089 := by
  apply lucas_primality 86937089 (3 : ZMod 86937089)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (7, 1), (127, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (7, 1), (127, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) = 86937089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_127
      · exact prime_eightyFiveCE_191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 86937089) ^ 43468544 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 86937089) ^ 12419584 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 86937089) ^ 684544 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 86937089) ^ 455168 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_91046083 : Nat.Prime 91046083 := by
  apply lucas_primality 91046083 (2 : ZMod 91046083)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (199, 1), (76253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (199, 1), (76253, 1)] : List FactorBlock).map factorBlockValue).prod) = 91046083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_199
      · exact prime_eightyFiveCE_76253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 91046083) ^ 45523041 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 91046083) ^ 30348694 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 91046083) ^ 457518 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 91046083) ^ 1194 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_93228139 : Nat.Prime 93228139 := by
  apply lucas_primality 93228139 (2 : ZMod 93228139)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1726447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1726447, 1)] : List FactorBlock).map factorBlockValue).prod) = 93228139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_1726447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 93228139) ^ 46614069 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 93228139) ^ 31076046 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 93228139) ^ 54 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_93398341 : Nat.Prime 93398341 := by
  apply lucas_primality 93398341 (2 : ZMod 93398341)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (103, 1), (127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (103, 1), (127, 1)] : List FactorBlock).map factorBlockValue).prod) = 93398341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_17
      · exact prime_eightyFiveCE_103
      · exact prime_eightyFiveCE_127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93398341) ^ 46699170 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 93398341) ^ 31132780 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 93398341) ^ 18679668 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 93398341) ^ 13342620 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 93398341) ^ 5494020 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 93398341) ^ 906780 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 93398341) ^ 735420 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_101132699 : Nat.Prime 101132699 := by
  apply lucas_primality 101132699 (2 : ZMod 101132699)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (163, 1), (310223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (163, 1), (310223, 1)] : List FactorBlock).map factorBlockValue).prod) = 101132699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_163
      · exact prime_eightyFiveCE_310223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 101132699) ^ 50566349 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 101132699) ^ 620446 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 101132699) ^ 326 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_103300027 : Nat.Prime 103300027 := by
  apply lucas_primality 103300027 (2 : ZMod 103300027)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17216671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17216671, 1)] : List FactorBlock).map factorBlockValue).prod) = 103300027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_17216671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 103300027) ^ 51650013 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 103300027) ^ 34433342 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 103300027) ^ 6 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_105479557 : Nat.Prime 105479557 := by
  apply lucas_primality 105479557 (2 : ZMod 105479557)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (13, 1), (13799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (13, 1), (13799, 1)] : List FactorBlock).map factorBlockValue).prod) = 105479557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_13799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 105479557) ^ 52739778 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 105479557) ^ 35159852 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 105479557) ^ 15068508 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 105479557) ^ 8113812 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 105479557) ^ 7644 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_105841973 : Nat.Prime 105841973 := by
  apply lucas_primality 105841973 (2 : ZMod 105841973)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (193, 1), (1931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (193, 1), (1931, 1)] : List FactorBlock).map factorBlockValue).prod) = 105841973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_71
      · exact prime_eightyFiveCE_193
      · exact prime_eightyFiveCE_1931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 105841973) ^ 52920986 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 105841973) ^ 1490732 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 105841973) ^ 548404 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 105841973) ^ 54812 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_107720189 : Nat.Prime 107720189 := by
  apply lucas_primality 107720189 (2 : ZMod 107720189)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (113, 1), (3557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (113, 1), (3557, 1)] : List FactorBlock).map factorBlockValue).prod) = 107720189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_67
      · exact prime_eightyFiveCE_113
      · exact prime_eightyFiveCE_3557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 107720189) ^ 53860094 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 107720189) ^ 1607764 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 107720189) ^ 953276 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 107720189) ^ 30284 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_109408591 : Nat.Prime 109408591 := by
  apply lucas_primality 109408591 (3 : ZMod 109408591)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (29, 1), (89, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (29, 1), (89, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) = 109408591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_29
      · exact prime_eightyFiveCE_89
      · exact prime_eightyFiveCE_157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 109408591) ^ 54704295 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 109408591) ^ 36469530 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 109408591) ^ 21881718 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 109408591) ^ 3772710 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 109408591) ^ 1229310 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 109408591) ^ 696870 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_122747857 : Nat.Prime 122747857 := by
  apply lucas_primality 122747857 (5 : ZMod 122747857)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (11, 1), (33211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (11, 1), (33211, 1)] : List FactorBlock).map factorBlockValue).prod) = 122747857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_33211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 122747857) ^ 61373928 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 122747857) ^ 40915952 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 122747857) ^ 17535408 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 122747857) ^ 11158896 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 122747857) ^ 3696 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_128283851 : Nat.Prime 128283851 := by
  apply lucas_primality 128283851 (2 : ZMod 128283851)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (53, 1), (48409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (53, 1), (48409, 1)] : List FactorBlock).map factorBlockValue).prod) = 128283851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_53
      · exact prime_eightyFiveCE_48409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 128283851) ^ 64141925 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 128283851) ^ 25656770 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 128283851) ^ 2420450 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 128283851) ^ 2650 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_130304329 : Nat.Prime 130304329 := by
  apply lucas_primality 130304329 (37 : ZMod 130304329)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 3), (11, 1), (1439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 3), (11, 1), (1439, 1)] : List FactorBlock).map factorBlockValue).prod) = 130304329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_1439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 130304329) ^ 65152164 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (37 : ZMod 130304329) ^ 43434776 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (37 : ZMod 130304329) ^ 18614904 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (37 : ZMod 130304329) ^ 11845848 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (37 : ZMod 130304329) ^ 90552 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_131642249 : Nat.Prime 131642249 := by
  apply lucas_primality 131642249 (3 : ZMod 131642249)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (53, 1), (13499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (53, 1), (13499, 1)] : List FactorBlock).map factorBlockValue).prod) = 131642249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_23
      · exact prime_eightyFiveCE_53
      · exact prime_eightyFiveCE_13499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 131642249) ^ 65821124 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 131642249) ^ 5723576 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 131642249) ^ 2483816 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 131642249) ^ 9752 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_146970727 : Nat.Prime 146970727 := by
  apply lucas_primality 146970727 (5 : ZMod 146970727)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1181, 1), (2963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1181, 1), (2963, 1)] : List FactorBlock).map factorBlockValue).prod) = 146970727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_1181
      · exact prime_eightyFiveCE_2963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 146970727) ^ 73485363 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 146970727) ^ 48990242 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 146970727) ^ 20995818 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 146970727) ^ 124446 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 146970727) ^ 49602 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_168490633 : Nat.Prime 168490633 := by
  apply lucas_primality 168490633 (7 : ZMod 168490633)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (151, 1), (2447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (151, 1), (2447, 1)] : List FactorBlock).map factorBlockValue).prod) = 168490633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_151
      · exact prime_eightyFiveCE_2447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 168490633) ^ 84245316 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 168490633) ^ 56163544 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 168490633) ^ 8867928 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 168490633) ^ 1115832 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 168490633) ^ 68856 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_170031821 : Nat.Prime 170031821 := by
  apply lucas_primality 170031821 (2 : ZMod 170031821)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (163, 1), (7451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (163, 1), (7451, 1)] : List FactorBlock).map factorBlockValue).prod) = 170031821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_163
      · exact prime_eightyFiveCE_7451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 170031821) ^ 85015910 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 170031821) ^ 34006364 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 170031821) ^ 24290260 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 170031821) ^ 1043140 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 170031821) ^ 22820 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_194932211 : Nat.Prime 194932211 := by
  apply lucas_primality 194932211 (6 : ZMod 194932211)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 2), (19, 1), (61, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 2), (19, 1), (61, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) = 194932211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_61
      · exact prime_eightyFiveCE_139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 194932211) ^ 97466105 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 194932211) ^ 38986442 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 194932211) ^ 17721110 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 194932211) ^ 10259590 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 194932211) ^ 3195610 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 194932211) ^ 1402390 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_209487337 : Nat.Prime 209487337 := by
  apply lucas_primality 209487337 (5 : ZMod 209487337)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (271, 1), (1039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (271, 1), (1039, 1)] : List FactorBlock).map factorBlockValue).prod) = 209487337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_31
      · exact prime_eightyFiveCE_271
      · exact prime_eightyFiveCE_1039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 209487337) ^ 104743668 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 209487337) ^ 69829112 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 209487337) ^ 6757656 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 209487337) ^ 773016 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 209487337) ^ 201624 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_219567473 : Nat.Prime 219567473 := by
  apply lucas_primality 219567473 (3 : ZMod 219567473)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (370891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (370891, 1)] : List FactorBlock).map factorBlockValue).prod) = 219567473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_37
      · exact prime_eightyFiveCE_370891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 219567473) ^ 109783736 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 219567473) ^ 5934256 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 219567473) ^ 592 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_225447913 : Nat.Prime 225447913 := by
  apply lucas_primality 225447913 (5 : ZMod 225447913)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (3131221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (3131221, 1)] : List FactorBlock).map factorBlockValue).prod) = 225447913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_3131221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 225447913) ^ 112723956 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 225447913) ^ 75149304 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 225447913) ^ 72 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_229545241 : Nat.Prime 229545241 := by
  apply lucas_primality 229545241 (22 : ZMod 229545241)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (89, 1), (21493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (89, 1), (21493, 1)] : List FactorBlock).map factorBlockValue).prod) = 229545241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_89
      · exact prime_eightyFiveCE_21493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 229545241) ^ 114772620 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (22 : ZMod 229545241) ^ 76515080 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (22 : ZMod 229545241) ^ 45909048 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (22 : ZMod 229545241) ^ 2579160 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (22 : ZMod 229545241) ^ 10680 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_233657531 : Nat.Prime 233657531 := by
  apply lucas_primality 233657531 (2 : ZMod 233657531)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (317, 1), (73709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (317, 1), (73709, 1)] : List FactorBlock).map factorBlockValue).prod) = 233657531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_317
      · exact prime_eightyFiveCE_73709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 233657531) ^ 116828765 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 233657531) ^ 46731506 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 233657531) ^ 737090 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 233657531) ^ 3170 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_239132683 : Nat.Prime 239132683 := by
  apply lucas_primality 239132683 (3 : ZMod 239132683)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (4428383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (4428383, 1)] : List FactorBlock).map factorBlockValue).prod) = 239132683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_4428383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 239132683) ^ 119566341 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 239132683) ^ 79710894 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 239132683) ^ 54 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_275978189 : Nat.Prime 275978189 := by
  apply lucas_primality 275978189 (2 : ZMod 275978189)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (167, 1), (413141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (167, 1), (413141, 1)] : List FactorBlock).map factorBlockValue).prod) = 275978189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_167
      · exact prime_eightyFiveCE_413141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 275978189) ^ 137989094 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 275978189) ^ 1652564 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 275978189) ^ 668 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_281669849 : Nat.Prime 281669849 := by
  apply lucas_primality 281669849 (3 : ZMod 281669849)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1237, 1), (28463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1237, 1), (28463, 1)] : List FactorBlock).map factorBlockValue).prod) = 281669849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_1237
      · exact prime_eightyFiveCE_28463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 281669849) ^ 140834924 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 281669849) ^ 227704 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 281669849) ^ 9896 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_381022657 : Nat.Prime 381022657 := by
  apply lucas_primality 381022657 (5 : ZMod 381022657)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (19, 1), (43, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (19, 1), (43, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) = 381022657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_43
      · exact prime_eightyFiveCE_347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 381022657) ^ 190511328 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 381022657) ^ 127007552 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 381022657) ^ 54431808 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 381022657) ^ 20053824 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 381022657) ^ 8860992 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 381022657) ^ 1098048 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_409471201 : Nat.Prime 409471201 := by
  apply lucas_primality 409471201 (14 : ZMod 409471201)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 4), (5, 2), (71, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 4), (5, 2), (71, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) = 409471201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_71
      · exact prime_eightyFiveCE_89
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 409471201) ^ 204735600 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 409471201) ^ 136490400 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 409471201) ^ 81894240 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 409471201) ^ 5767200 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 409471201) ^ 4600800 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_410566141 : Nat.Prime 410566141 := by
  apply lucas_primality 410566141 (2 : ZMod 410566141)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (83, 1), (27481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (83, 1), (27481, 1)] : List FactorBlock).map factorBlockValue).prod) = 410566141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_83
      · exact prime_eightyFiveCE_27481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 410566141) ^ 205283070 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 410566141) ^ 136855380 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 410566141) ^ 82113228 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 410566141) ^ 4946580 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 410566141) ^ 14940 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_417542549 : Nat.Prime 417542549 := by
  apply lucas_primality 417542549 (2 : ZMod 417542549)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (2220971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (2220971, 1)] : List FactorBlock).map factorBlockValue).prod) = 417542549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_47
      · exact prime_eightyFiveCE_2220971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 417542549) ^ 208771274 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 417542549) ^ 8883884 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 417542549) ^ 188 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_438746899 : Nat.Prime 438746899 := by
  apply lucas_primality 438746899 (10 : ZMod 438746899)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (3848657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (3848657, 1)] : List FactorBlock).map factorBlockValue).prod) = 438746899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_3848657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 438746899) ^ 219373449 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 438746899) ^ 146248966 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 438746899) ^ 23091942 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 438746899) ^ 114 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_488019913 : Nat.Prime 488019913 := by
  apply lucas_primality 488019913 (5 : ZMod 488019913)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (20334163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (20334163, 1)] : List FactorBlock).map factorBlockValue).prod) = 488019913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_20334163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 488019913) ^ 244009956 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 488019913) ^ 162673304 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 488019913) ^ 24 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_511017737 : Nat.Prime 511017737 := by
  apply lucas_primality 511017737 (3 : ZMod 511017737)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (431, 1), (148207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (431, 1), (148207, 1)] : List FactorBlock).map factorBlockValue).prod) = 511017737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_431
      · exact prime_eightyFiveCE_148207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 511017737) ^ 255508868 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 511017737) ^ 1185656 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 511017737) ^ 3448 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_512637481 : Nat.Prime 512637481 := by
  apply lucas_primality 512637481 (13 : ZMod 512637481)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (19, 1), (149, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (19, 1), (149, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) = 512637481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_149
      · exact prime_eightyFiveCE_503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 512637481) ^ 256318740 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (13 : ZMod 512637481) ^ 170879160 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (13 : ZMod 512637481) ^ 102527496 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (13 : ZMod 512637481) ^ 26980920 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (13 : ZMod 512637481) ^ 3440520 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (13 : ZMod 512637481) ^ 1019160 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_587216129 : Nat.Prime 587216129 := by
  apply lucas_primality 587216129 (3 : ZMod 587216129)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (19, 1), (23, 1), (29, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (19, 1), (23, 1), (29, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) = 587216129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_23
      · exact prime_eightyFiveCE_29
      · exact prime_eightyFiveCE_181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 587216129) ^ 293608064 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 587216129) ^ 30906112 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 587216129) ^ 25531136 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 587216129) ^ 20248832 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 587216129) ^ 3244288 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_604894079 : Nat.Prime 604894079 := by
  apply lucas_primality 604894079 (11 : ZMod 604894079)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (5126221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (5126221, 1)] : List FactorBlock).map factorBlockValue).prod) = 604894079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_59
      · exact prime_eightyFiveCE_5126221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 604894079) ^ 302447039 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 604894079) ^ 10252442 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 604894079) ^ 118 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_648522073 : Nat.Prime 648522073 := by
  apply lucas_primality 648522073 (5 : ZMod 648522073)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (11, 1), (73, 1), (3739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (11, 1), (73, 1), (3739, 1)] : List FactorBlock).map factorBlockValue).prod) = 648522073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_73
      · exact prime_eightyFiveCE_3739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 648522073) ^ 324261036 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 648522073) ^ 216174024 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 648522073) ^ 58956552 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 648522073) ^ 8883864 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 648522073) ^ 173448 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_711562889 : Nat.Prime 711562889 := by
  apply lucas_primality 711562889 (3 : ZMod 711562889)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (997, 1), (89213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (997, 1), (89213, 1)] : List FactorBlock).map factorBlockValue).prod) = 711562889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_997
      · exact prime_eightyFiveCE_89213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 711562889) ^ 355781444 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 711562889) ^ 713704 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 711562889) ^ 7976 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_743240737 : Nat.Prime 743240737 := by
  apply lucas_primality 743240737 (10 : ZMod 743240737)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (7, 1), (317, 1), (1163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (7, 1), (317, 1), (1163, 1)] : List FactorBlock).map factorBlockValue).prod) = 743240737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_317
      · exact prime_eightyFiveCE_1163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 743240737) ^ 371620368 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 743240737) ^ 247746912 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 743240737) ^ 106177248 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 743240737) ^ 2344608 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 743240737) ^ 639072 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_930548819 : Nat.Prime 930548819 := by
  apply lucas_primality 930548819 (2 : ZMod 930548819)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (227, 1), (2049667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (227, 1), (2049667, 1)] : List FactorBlock).map factorBlockValue).prod) = 930548819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_227
      · exact prime_eightyFiveCE_2049667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 930548819) ^ 465274409 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 930548819) ^ 4099334 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 930548819) ^ 454 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_979833073 : Nat.Prime 979833073 := by
  apply lucas_primality 979833073 (10 : ZMod 979833073)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (3323, 1), (6143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (3323, 1), (6143, 1)] : List FactorBlock).map factorBlockValue).prod) = 979833073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_3323
      · exact prime_eightyFiveCE_6143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 979833073) ^ 489916536 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 979833073) ^ 326611024 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 979833073) ^ 294864 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 979833073) ^ 159504 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_980939051 : Nat.Prime 980939051 := by
  apply lucas_primality 980939051 (2 : ZMod 980939051)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (13, 1), (79, 1), (2729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (13, 1), (79, 1), (2729, 1)] : List FactorBlock).map factorBlockValue).prod) = 980939051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_79
      · exact prime_eightyFiveCE_2729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 980939051) ^ 490469525 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 980939051) ^ 196187810 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 980939051) ^ 140134150 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 980939051) ^ 75456850 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 980939051) ^ 12416950 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 980939051) ^ 359450 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_999267827 : Nat.Prime 999267827 := by
  apply lucas_primality 999267827 (2 : ZMod 999267827)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (41, 1), (393103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (41, 1), (393103, 1)] : List FactorBlock).map factorBlockValue).prod) = 999267827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_31
      · exact prime_eightyFiveCE_41
      · exact prime_eightyFiveCE_393103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 999267827) ^ 499633913 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 999267827) ^ 32234446 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 999267827) ^ 24372386 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 999267827) ^ 2542 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1121424299 : Nat.Prime 1121424299 := by
  apply lucas_primality 1121424299 (2 : ZMod 1121424299)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1307, 1), (429007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1307, 1), (429007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1121424299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_1307
      · exact prime_eightyFiveCE_429007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1121424299) ^ 560712149 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1121424299) ^ 858014 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1121424299) ^ 2614 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1250661883 : Nat.Prime 1250661883 := by
  apply lucas_primality 1250661883 (3 : ZMod 1250661883)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (53, 1), (231347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (53, 1), (231347, 1)] : List FactorBlock).map factorBlockValue).prod) = 1250661883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_17
      · exact prime_eightyFiveCE_53
      · exact prime_eightyFiveCE_231347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1250661883) ^ 625330941 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1250661883) ^ 416887294 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1250661883) ^ 73568346 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1250661883) ^ 23597394 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1250661883) ^ 5406 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1442871803 : Nat.Prime 1442871803 := by
  apply lucas_primality 1442871803 (2 : ZMod 1442871803)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1103, 1), (654067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1103, 1), (654067, 1)] : List FactorBlock).map factorBlockValue).prod) = 1442871803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_1103
      · exact prime_eightyFiveCE_654067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1442871803) ^ 721435901 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1442871803) ^ 1308134 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1442871803) ^ 2206 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1524090629 : Nat.Prime 1524090629 := by
  apply lucas_primality 1524090629 (2 : ZMod 1524090629)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (381022657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (381022657, 1)] : List FactorBlock).map factorBlockValue).prod) = 1524090629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_381022657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1524090629) ^ 762045314 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1524090629) ^ 4 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1620350987 : Nat.Prime 1620350987 := by
  apply lucas_primality 1620350987 (2 : ZMod 1620350987)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3257, 1), (248749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3257, 1), (248749, 1)] : List FactorBlock).map factorBlockValue).prod) = 1620350987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3257
      · exact prime_eightyFiveCE_248749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1620350987) ^ 810175493 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1620350987) ^ 497498 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1620350987) ^ 6514 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1764857267 : Nat.Prime 1764857267 := by
  apply lucas_primality 1764857267 (2 : ZMod 1764857267)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1621, 1), (544373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1621, 1), (544373, 1)] : List FactorBlock).map factorBlockValue).prod) = 1764857267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_1621
      · exact prime_eightyFiveCE_544373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1764857267) ^ 882428633 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1764857267) ^ 1088746 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1764857267) ^ 3242 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1788736493 : Nat.Prime 1788736493 := by
  apply lucas_primality 1788736493 (2 : ZMod 1788736493)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19051, 1), (23473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19051, 1), (23473, 1)] : List FactorBlock).map factorBlockValue).prod) = 1788736493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_19051
      · exact prime_eightyFiveCE_23473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1788736493) ^ 894368246 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1788736493) ^ 93892 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1788736493) ^ 76204 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1869260249 : Nat.Prime 1869260249 := by
  apply lucas_primality 1869260249 (3 : ZMod 1869260249)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (233657531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (233657531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1869260249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_233657531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1869260249) ^ 934630124 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1869260249) ^ 8 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1888576037 : Nat.Prime 1888576037 := by
  apply lucas_primality 1888576037 (2 : ZMod 1888576037)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (293, 1), (94789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (293, 1), (94789, 1)] : List FactorBlock).map factorBlockValue).prod) = 1888576037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_17
      · exact prime_eightyFiveCE_293
      · exact prime_eightyFiveCE_94789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1888576037) ^ 944288018 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1888576037) ^ 111092708 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1888576037) ^ 6445652 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1888576037) ^ 19924 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_2242848599 : Nat.Prime 2242848599 := by
  apply lucas_primality 2242848599 (31 : ZMod 2242848599)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1121424299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1121424299, 1)] : List FactorBlock).map factorBlockValue).prod) = 2242848599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_1121424299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (31 : ZMod 2242848599) ^ 1121424299 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (31 : ZMod 2242848599) ^ 2 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_2907231461 : Nat.Prime 2907231461 := by
  apply lucas_primality 2907231461 (3 : ZMod 2907231461)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (31, 1), (669869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (31, 1), (669869, 1)] : List FactorBlock).map factorBlockValue).prod) = 2907231461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_31
      · exact prime_eightyFiveCE_669869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2907231461) ^ 1453615730 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2907231461) ^ 581446292 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2907231461) ^ 415318780 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2907231461) ^ 93781660 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2907231461) ^ 4340 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_2962735211 : Nat.Prime 2962735211 := by
  apply lucas_primality 2962735211 (6 : ZMod 2962735211)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1103, 1), (268607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1103, 1), (268607, 1)] : List FactorBlock).map factorBlockValue).prod) = 2962735211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_1103
      · exact prime_eightyFiveCE_268607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2962735211) ^ 1481367605 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2962735211) ^ 592547042 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2962735211) ^ 2686070 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2962735211) ^ 11030 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_3095566823 : Nat.Prime 3095566823 := by
  apply lucas_primality 3095566823 (5 : ZMod 3095566823)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (91046083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (91046083, 1)] : List FactorBlock).map factorBlockValue).prod) = 3095566823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_17
      · exact prime_eightyFiveCE_91046083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3095566823) ^ 1547783411 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 3095566823) ^ 182092166 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 3095566823) ^ 34 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_3644953001 : Nat.Prime 3644953001 := by
  apply lucas_primality 3644953001 (3 : ZMod 3644953001)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (13, 1), (17, 1), (16493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (13, 1), (17, 1), (16493, 1)] : List FactorBlock).map factorBlockValue).prod) = 3644953001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_17
      · exact prime_eightyFiveCE_16493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3644953001) ^ 1822476500 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3644953001) ^ 728990600 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3644953001) ^ 280381000 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3644953001) ^ 214409000 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3644953001) ^ 221000 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_3786579791 : Nat.Prime 3786579791 := by
  apply lucas_primality 3786579791 (13 : ZMod 3786579791)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (54093997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (54093997, 1)] : List FactorBlock).map factorBlockValue).prod) = 3786579791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_54093997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 3786579791) ^ 1893289895 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (13 : ZMod 3786579791) ^ 757315958 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (13 : ZMod 3786579791) ^ 540939970 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (13 : ZMod 3786579791) ^ 70 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_4120366331 : Nat.Prime 4120366331 := by
  apply lucas_primality 4120366331 (2 : ZMod 4120366331)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (24237449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (24237449, 1)] : List FactorBlock).map factorBlockValue).prod) = 4120366331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_17
      · exact prime_eightyFiveCE_24237449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4120366331) ^ 2060183165 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4120366331) ^ 824073266 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4120366331) ^ 242374490 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4120366331) ^ 170 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_4722462781 : Nat.Prime 4722462781 := by
  apply lucas_primality 4722462781 (2 : ZMod 4722462781)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (467, 1), (24077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (467, 1), (24077, 1)] : List FactorBlock).map factorBlockValue).prod) = 4722462781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_467
      · exact prime_eightyFiveCE_24077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4722462781) ^ 2361231390 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4722462781) ^ 1574154260 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4722462781) ^ 944492556 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4722462781) ^ 674637540 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4722462781) ^ 10112340 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4722462781) ^ 196140 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_4724052017 : Nat.Prime 4724052017 := by
  apply lucas_primality 4724052017 (3 : ZMod 4724052017)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (571, 1), (517081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (571, 1), (517081, 1)] : List FactorBlock).map factorBlockValue).prod) = 4724052017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_571
      · exact prime_eightyFiveCE_517081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4724052017) ^ 2362026008 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4724052017) ^ 8273296 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4724052017) ^ 9136 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_5814462923 : Nat.Prime 5814462923 := by
  apply lucas_primality 5814462923 (2 : ZMod 5814462923)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2907231461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2907231461, 1)] : List FactorBlock).map factorBlockValue).prod) = 5814462923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_2907231461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5814462923) ^ 2907231461 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5814462923) ^ 2 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_5878998439 : Nat.Prime 5878998439 := by
  apply lucas_primality 5878998439 (3 : ZMod 5878998439)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (979833073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (979833073, 1)] : List FactorBlock).map factorBlockValue).prod) = 5878998439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_979833073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5878998439) ^ 2939499219 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5878998439) ^ 1959666146 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5878998439) ^ 6 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_5962322281 : Nat.Prime 5962322281 := by
  apply lucas_primality 5962322281 (21 : ZMod 5962322281)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17, 1), (29, 1), (97, 1), (1039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17, 1), (29, 1), (97, 1), (1039, 1)] : List FactorBlock).map factorBlockValue).prod) = 5962322281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_17
      · exact prime_eightyFiveCE_29
      · exact prime_eightyFiveCE_97
      · exact prime_eightyFiveCE_1039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 5962322281) ^ 2981161140 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (21 : ZMod 5962322281) ^ 1987440760 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (21 : ZMod 5962322281) ^ 1192464456 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (21 : ZMod 5962322281) ^ 350724840 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (21 : ZMod 5962322281) ^ 205597320 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (21 : ZMod 5962322281) ^ 61467240 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (21 : ZMod 5962322281) ^ 5738520 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_6062895001 : Nat.Prime 6062895001 := by
  apply lucas_primality 6062895001 (23 : ZMod 6062895001)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 4), (134731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 4), (134731, 1)] : List FactorBlock).map factorBlockValue).prod) = 6062895001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_134731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 6062895001) ^ 3031447500 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (23 : ZMod 6062895001) ^ 2020965000 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (23 : ZMod 6062895001) ^ 1212579000 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (23 : ZMod 6062895001) ^ 45000 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_6191133647 : Nat.Prime 6191133647 := by
  apply lucas_primality 6191133647 (5 : ZMod 6191133647)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3095566823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3095566823, 1)] : List FactorBlock).map factorBlockValue).prod) = 6191133647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3095566823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 6191133647) ^ 3095566823 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 6191133647) ^ 2 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_6586984913 : Nat.Prime 6586984913 := by
  apply lucas_primality 6586984913 (3 : ZMod 6586984913)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (83, 1), (191, 1), (25969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (83, 1), (191, 1), (25969, 1)] : List FactorBlock).map factorBlockValue).prod) = 6586984913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_83
      · exact prime_eightyFiveCE_191
      · exact prime_eightyFiveCE_25969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6586984913) ^ 3293492456 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6586984913) ^ 79361264 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6586984913) ^ 34486832 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6586984913) ^ 253648 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_6624282853 : Nat.Prime 6624282853 := by
  apply lucas_primality 6624282853 (2 : ZMod 6624282853)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (16727987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (16727987, 1)] : List FactorBlock).map factorBlockValue).prod) = 6624282853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_16727987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6624282853) ^ 3312141426 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6624282853) ^ 2208094284 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6624282853) ^ 602207532 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6624282853) ^ 396 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_6914994467 : Nat.Prime 6914994467 := by
  apply lucas_primality 6914994467 (2 : ZMod 6914994467)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (1987, 1), (9721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (1987, 1), (9721, 1)] : List FactorBlock).map factorBlockValue).prod) = 6914994467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_179
      · exact prime_eightyFiveCE_1987
      · exact prime_eightyFiveCE_9721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6914994467) ^ 3457497233 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6914994467) ^ 38631254 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6914994467) ^ 3480118 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6914994467) ^ 711346 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_8240732663 : Nat.Prime 8240732663 := by
  apply lucas_primality 8240732663 (5 : ZMod 8240732663)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4120366331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4120366331, 1)] : List FactorBlock).map factorBlockValue).prod) = 8240732663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_4120366331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 8240732663) ^ 4120366331 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 8240732663) ^ 2 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_8353289083 : Nat.Prime 8353289083 := by
  apply lucas_primality 8353289083 (2 : ZMod 8353289083)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (103, 1), (795097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (103, 1), (795097, 1)] : List FactorBlock).map factorBlockValue).prod) = 8353289083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_17
      · exact prime_eightyFiveCE_103
      · exact prime_eightyFiveCE_795097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8353289083) ^ 4176644541 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 8353289083) ^ 2784429694 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 8353289083) ^ 491369946 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 8353289083) ^ 81099894 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 8353289083) ^ 10506 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_8837647057 : Nat.Prime 8837647057 := by
  apply lucas_primality 8837647057 (10 : ZMod 8837647057)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 2), (101, 1), (12401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 2), (101, 1), (12401, 1)] : List FactorBlock).map factorBlockValue).prod) = 8837647057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_101
      · exact prime_eightyFiveCE_12401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 8837647057) ^ 4418823528 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 8837647057) ^ 2945882352 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 8837647057) ^ 1262521008 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 8837647057) ^ 87501456 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 8837647057) ^ 712656 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_10249369219 : Nat.Prime 10249369219 := by
  apply lucas_primality 10249369219 (10 : ZMod 10249369219)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (137, 1), (377843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (137, 1), (377843, 1)] : List FactorBlock).map factorBlockValue).prod) = 10249369219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_137
      · exact prime_eightyFiveCE_377843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10249369219) ^ 5124684609 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 10249369219) ^ 3416456406 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 10249369219) ^ 931760838 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 10249369219) ^ 74812914 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 10249369219) ^ 27126 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_11649569927 : Nat.Prime 11649569927 := by
  apply lucas_primality 11649569927 (5 : ZMod 11649569927)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (86937089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (86937089, 1)] : List FactorBlock).map factorBlockValue).prod) = 11649569927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_67
      · exact prime_eightyFiveCE_86937089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 11649569927) ^ 5824784963 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 11649569927) ^ 173874178 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 11649569927) ^ 134 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_12142339087 : Nat.Prime 12142339087 := by
  apply lucas_primality 12142339087 (3 : ZMod 12142339087)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (379, 1), (64333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (379, 1), (64333, 1)] : List FactorBlock).map factorBlockValue).prod) = 12142339087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_83
      · exact prime_eightyFiveCE_379
      · exact prime_eightyFiveCE_64333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12142339087) ^ 6071169543 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12142339087) ^ 4047446362 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12142339087) ^ 146293242 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12142339087) ^ 32037834 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12142339087) ^ 188742 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_13624325213 : Nat.Prime 13624325213 := by
  apply lucas_primality 13624325213 (2 : ZMod 13624325213)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (653, 1), (274529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (653, 1), (274529, 1)] : List FactorBlock).map factorBlockValue).prod) = 13624325213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_653
      · exact prime_eightyFiveCE_274529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13624325213) ^ 6812162606 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13624325213) ^ 717069748 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13624325213) ^ 20864204 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13624325213) ^ 49628 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_14114486479 : Nat.Prime 14114486479 := by
  apply lucas_primality 14114486479 (7 : ZMod 14114486479)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (313, 1), (1051, 1), (7151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (313, 1), (1051, 1), (7151, 1)] : List FactorBlock).map factorBlockValue).prod) = 14114486479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_313
      · exact prime_eightyFiveCE_1051
      · exact prime_eightyFiveCE_7151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14114486479) ^ 7057243239 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 14114486479) ^ 4704828826 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 14114486479) ^ 45094206 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 14114486479) ^ 13429578 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 14114486479) ^ 1973778 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_14769781331 : Nat.Prime 14769781331 := by
  apply lucas_primality 14769781331 (2 : ZMod 14769781331)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (293, 1), (947, 1), (5323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (293, 1), (947, 1), (5323, 1)] : List FactorBlock).map factorBlockValue).prod) = 14769781331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_293
      · exact prime_eightyFiveCE_947
      · exact prime_eightyFiveCE_5323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14769781331) ^ 7384890665 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14769781331) ^ 2953956266 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14769781331) ^ 50408810 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14769781331) ^ 15596390 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14769781331) ^ 2774710 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_17649765151 : Nat.Prime 17649765151 := by
  apply lucas_primality 17649765151 (14 : ZMod 17649765151)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (101, 1), (1165001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (101, 1), (1165001, 1)] : List FactorBlock).map factorBlockValue).prod) = 17649765151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_101
      · exact prime_eightyFiveCE_1165001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 17649765151) ^ 8824882575 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 17649765151) ^ 5883255050 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 17649765151) ^ 3529953030 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 17649765151) ^ 174750150 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 17649765151) ^ 15150 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_19452685979 : Nat.Prime 19452685979 := by
  apply lucas_primality 19452685979 (2 : ZMod 19452685979)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (43, 1), (59, 1), (348527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (43, 1), (59, 1), (348527, 1)] : List FactorBlock).map factorBlockValue).prod) = 19452685979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_43
      · exact prime_eightyFiveCE_59
      · exact prime_eightyFiveCE_348527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19452685979) ^ 9726342989 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 19452685979) ^ 1768425998 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 19452685979) ^ 452388046 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 19452685979) ^ 329706542 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 19452685979) ^ 55814 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_19466137357 : Nat.Prime 19466137357 := by
  apply lucas_primality 19466137357 (2 : ZMod 19466137357)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8273, 1), (196081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8273, 1), (196081, 1)] : List FactorBlock).map factorBlockValue).prod) = 19466137357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_8273
      · exact prime_eightyFiveCE_196081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19466137357) ^ 9733068678 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 19466137357) ^ 6488712452 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 19466137357) ^ 2352972 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 19466137357) ^ 99276 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_21702863803 : Nat.Prime 21702863803 := by
  apply lucas_primality 21702863803 (2 : ZMod 21702863803)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1049, 1), (149921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1049, 1), (149921, 1)] : List FactorBlock).map factorBlockValue).prod) = 21702863803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_23
      · exact prime_eightyFiveCE_1049
      · exact prime_eightyFiveCE_149921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21702863803) ^ 10851431901 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 21702863803) ^ 7234287934 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 21702863803) ^ 943602774 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 21702863803) ^ 20689098 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 21702863803) ^ 144762 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_22726005941 : Nat.Prime 22726005941 := by
  apply lucas_primality 22726005941 (3 : ZMod 22726005941)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (103300027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (103300027, 1)] : List FactorBlock).map factorBlockValue).prod) = 22726005941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_103300027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22726005941) ^ 11363002970 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 22726005941) ^ 4545201188 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 22726005941) ^ 2066000540 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 22726005941) ^ 220 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_23253648329 : Nat.Prime 23253648329 := by
  apply lucas_primality 23253648329 (3 : ZMod 23253648329)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (103, 1), (197, 1), (4621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (103, 1), (197, 1), (4621, 1)] : List FactorBlock).map factorBlockValue).prod) = 23253648329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_31
      · exact prime_eightyFiveCE_103
      · exact prime_eightyFiveCE_197
      · exact prime_eightyFiveCE_4621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23253648329) ^ 11626824164 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23253648329) ^ 750117688 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23253648329) ^ 225763576 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23253648329) ^ 118038824 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23253648329) ^ 5032168 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_24577773697 : Nat.Prime 24577773697 := by
  apply lucas_primality 24577773697 (10 : ZMod 24577773697)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (7, 1), (137, 1), (22247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (7, 1), (137, 1), (22247, 1)] : List FactorBlock).map factorBlockValue).prod) = 24577773697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_137
      · exact prime_eightyFiveCE_22247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 24577773697) ^ 12288886848 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 24577773697) ^ 8192591232 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 24577773697) ^ 3511110528 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 24577773697) ^ 179399808 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 24577773697) ^ 1104768 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_24838037011 : Nat.Prime 24838037011 := by
  apply lucas_primality 24838037011 (2 : ZMod 24838037011)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (275978189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (275978189, 1)] : List FactorBlock).map factorBlockValue).prod) = 24838037011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_275978189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24838037011) ^ 12419018505 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 24838037011) ^ 8279345670 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 24838037011) ^ 4967607402 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 24838037011) ^ 90 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_33956840987 : Nat.Prime 33956840987 := by
  apply lucas_primality 33956840987 (2 : ZMod 33956840987)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (239132683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (239132683, 1)] : List FactorBlock).map factorBlockValue).prod) = 33956840987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_71
      · exact prime_eightyFiveCE_239132683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33956840987) ^ 16978420493 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33956840987) ^ 478265366 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33956840987) ^ 142 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_37616472181 : Nat.Prime 37616472181 := by
  apply lucas_primality 37616472181 (2 : ZMod 37616472181)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (2843, 1), (10501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (2843, 1), (10501, 1)] : List FactorBlock).map factorBlockValue).prod) = 37616472181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_2843
      · exact prime_eightyFiveCE_10501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37616472181) ^ 18808236090 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37616472181) ^ 12538824060 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37616472181) ^ 7523294436 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37616472181) ^ 5373781740 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37616472181) ^ 13231260 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37616472181) ^ 3582180 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_45438957493 : Nat.Prime 45438957493 := by
  apply lucas_primality 45438957493 (2 : ZMod 45438957493)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3786579791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3786579791, 1)] : List FactorBlock).map factorBlockValue).prod) = 45438957493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_3786579791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45438957493) ^ 22719478746 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 45438957493) ^ 15146319164 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 45438957493) ^ 12 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_49173391297 : Nat.Prime 49173391297 := by
  apply lucas_primality 49173391297 (11 : ZMod 49173391297)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (47, 1), (71, 1), (25583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (47, 1), (71, 1), (25583, 1)] : List FactorBlock).map factorBlockValue).prod) = 49173391297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_47
      · exact prime_eightyFiveCE_71
      · exact prime_eightyFiveCE_25583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 49173391297) ^ 24586695648 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 49173391297) ^ 16391130432 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 49173391297) ^ 1046242368 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 49173391297) ^ 692582976 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 49173391297) ^ 1922112 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_62598285517 : Nat.Prime 62598285517 := by
  apply lucas_primality 62598285517 (2 : ZMod 62598285517)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (541, 1), (741721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (541, 1), (741721, 1)] : List FactorBlock).map factorBlockValue).prod) = 62598285517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_541
      · exact prime_eightyFiveCE_741721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 62598285517) ^ 31299142758 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 62598285517) ^ 20866095172 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 62598285517) ^ 4815252732 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 62598285517) ^ 115708476 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 62598285517) ^ 84396 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_62814480863 : Nat.Prime 62814480863 := by
  apply lucas_primality 62814480863 (5 : ZMod 62814480863)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (59, 1), (76046587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (59, 1), (76046587, 1)] : List FactorBlock).map factorBlockValue).prod) = 62814480863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_59
      · exact prime_eightyFiveCE_76046587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 62814480863) ^ 31407240431 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 62814480863) ^ 8973497266 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 62814480863) ^ 1064652218 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 62814480863) ^ 826 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_76196909359 : Nat.Prime 76196909359 := by
  apply lucas_primality 76196909359 (3 : ZMod 76196909359)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (31, 1), (199, 1), (228733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (31, 1), (199, 1), (228733, 1)] : List FactorBlock).map factorBlockValue).prod) = 76196909359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_31
      · exact prime_eightyFiveCE_199
      · exact prime_eightyFiveCE_228733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 76196909359) ^ 38098454679 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 76196909359) ^ 25398969786 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 76196909359) ^ 2457964818 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 76196909359) ^ 382899042 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 76196909359) ^ 333126 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_81745951279 : Nat.Prime 81745951279 := by
  apply lucas_primality 81745951279 (3 : ZMod 81745951279)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13624325213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13624325213, 1)] : List FactorBlock).map factorBlockValue).prod) = 81745951279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_13624325213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 81745951279) ^ 40872975639 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 81745951279) ^ 27248650426 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 81745951279) ^ 6 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_90247001641 : Nat.Prime 90247001641 := by
  apply lucas_primality 90247001641 (7 : ZMod 90247001641)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (23, 1), (43, 1), (760423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (23, 1), (43, 1), (760423, 1)] : List FactorBlock).map factorBlockValue).prod) = 90247001641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_23
      · exact prime_eightyFiveCE_43
      · exact prime_eightyFiveCE_760423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 90247001641) ^ 45123500820 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 90247001641) ^ 30082333880 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 90247001641) ^ 18049400328 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 90247001641) ^ 3923782680 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 90247001641) ^ 2098767480 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 90247001641) ^ 118680 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_94776322793 : Nat.Prime 94776322793 := by
  apply lucas_primality 94776322793 (3 : ZMod 94776322793)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (48619, 1), (243671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (48619, 1), (243671, 1)] : List FactorBlock).map factorBlockValue).prod) = 94776322793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_48619
      · exact prime_eightyFiveCE_243671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 94776322793) ^ 47388161396 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 94776322793) ^ 1949368 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 94776322793) ^ 388952 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_95437936553 : Nat.Prime 95437936553 := by
  apply lucas_primality 95437936553 (3 : ZMod 95437936553)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (53, 1), (32155639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (53, 1), (32155639, 1)] : List FactorBlock).map factorBlockValue).prod) = 95437936553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_53
      · exact prime_eightyFiveCE_32155639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 95437936553) ^ 47718968276 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 95437936553) ^ 13633990936 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 95437936553) ^ 1800715784 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 95437936553) ^ 2968 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_100538903327 : Nat.Prime 100538903327 := by
  apply lucas_primality 100538903327 (5 : ZMod 100538903327)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23819, 1), (2110477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23819, 1), (2110477, 1)] : List FactorBlock).map factorBlockValue).prod) = 100538903327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_23819
      · exact prime_eightyFiveCE_2110477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 100538903327) ^ 50269451663 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 100538903327) ^ 4220954 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 100538903327) ^ 47638 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_103186742653 : Nat.Prime 103186742653 := by
  apply lucas_primality 103186742653 (2 : ZMod 103186742653)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (409471201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (409471201, 1)] : List FactorBlock).map factorBlockValue).prod) = 103186742653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_409471201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 103186742653) ^ 51593371326 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 103186742653) ^ 34395580884 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 103186742653) ^ 14740963236 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 103186742653) ^ 252 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_150010418611 : Nat.Prime 150010418611 := by
  apply lucas_primality 150010418611 (2 : ZMod 150010418611)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (13, 1), (19, 1), (1123, 1), (2003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (13, 1), (19, 1), (1123, 1), (2003, 1)] : List FactorBlock).map factorBlockValue).prod) = 150010418611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_1123
      · exact prime_eightyFiveCE_2003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 150010418611) ^ 75005209305 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 150010418611) ^ 50003472870 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 150010418611) ^ 30002083722 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 150010418611) ^ 11539262970 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 150010418611) ^ 7895285190 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 150010418611) ^ 133580070 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 150010418611) ^ 74892870 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_162488905049 : Nat.Prime 162488905049 := by
  apply lucas_primality 162488905049 (3 : ZMod 162488905049)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (25747, 1), (788873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (25747, 1), (788873, 1)] : List FactorBlock).map factorBlockValue).prod) = 162488905049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_25747
      · exact prime_eightyFiveCE_788873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 162488905049) ^ 81244452524 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 162488905049) ^ 6310984 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 162488905049) ^ 205976 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_213761627447 : Nat.Prime 213761627447 := by
  apply lucas_primality 213761627447 (5 : ZMod 213761627447)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (97, 1), (6397, 1), (7489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (97, 1), (6397, 1), (7489, 1)] : List FactorBlock).map factorBlockValue).prod) = 213761627447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_23
      · exact prime_eightyFiveCE_97
      · exact prime_eightyFiveCE_6397
      · exact prime_eightyFiveCE_7489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 213761627447) ^ 106880813723 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 213761627447) ^ 9293983802 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 213761627447) ^ 2203728118 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 213761627447) ^ 33415918 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 213761627447) ^ 28543414 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_233663320853 : Nat.Prime 233663320853 := by
  apply lucas_primality 233663320853 (2 : ZMod 233663320853)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (191, 1), (23526311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (191, 1), (23526311, 1)] : List FactorBlock).map factorBlockValue).prod) = 233663320853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_191
      · exact prime_eightyFiveCE_23526311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 233663320853) ^ 116831660426 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 233663320853) ^ 17974101604 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 233663320853) ^ 1223368172 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 233663320853) ^ 9932 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_241836781789 : Nat.Prime 241836781789 := by
  apply lucas_primality 241836781789 (2 : ZMod 241836781789)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (29, 1), (11030687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (29, 1), (11030687, 1)] : List FactorBlock).map factorBlockValue).prod) = 241836781789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_29
      · exact prime_eightyFiveCE_11030687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 241836781789) ^ 120918390894 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 241836781789) ^ 80612260596 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 241836781789) ^ 34548111684 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 241836781789) ^ 8339199372 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 241836781789) ^ 21924 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_304787637437 : Nat.Prime 304787637437 := by
  apply lucas_primality 304787637437 (2 : ZMod 304787637437)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (76196909359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (76196909359, 1)] : List FactorBlock).map factorBlockValue).prod) = 304787637437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_76196909359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 304787637437) ^ 152393818718 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 304787637437) ^ 4 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_324977810099 : Nat.Prime 324977810099 := by
  apply lucas_primality 324977810099 (2 : ZMod 324977810099)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (162488905049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (162488905049, 1)] : List FactorBlock).map factorBlockValue).prod) = 324977810099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_162488905049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 324977810099) ^ 162488905049 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 324977810099) ^ 2 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_473521365257 : Nat.Prime 473521365257 := by
  apply lucas_primality 473521365257 (3 : ZMod 473521365257)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (8093, 1), (7313749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (8093, 1), (7313749, 1)] : List FactorBlock).map factorBlockValue).prod) = 473521365257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_8093
      · exact prime_eightyFiveCE_7313749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 473521365257) ^ 236760682628 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 473521365257) ^ 58509992 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 473521365257) ^ 64744 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_485134414291 : Nat.Prime 485134414291 := by
  apply lucas_primality 485134414291 (2 : ZMod 485134414291)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (41, 1), (43824247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (41, 1), (43824247, 1)] : List FactorBlock).map factorBlockValue).prod) = 485134414291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_41
      · exact prime_eightyFiveCE_43824247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 485134414291) ^ 242567207145 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 485134414291) ^ 161711471430 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 485134414291) ^ 97026882858 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 485134414291) ^ 11832546690 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 485134414291) ^ 11070 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_605099828131 : Nat.Prime 605099828131 := by
  apply lucas_primality 605099828131 (2 : ZMod 605099828131)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (109, 1), (151, 1), (175067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (109, 1), (151, 1), (175067, 1)] : List FactorBlock).map factorBlockValue).prod) = 605099828131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_109
      · exact prime_eightyFiveCE_151
      · exact prime_eightyFiveCE_175067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 605099828131) ^ 302549914065 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 605099828131) ^ 201699942710 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 605099828131) ^ 121019965626 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 605099828131) ^ 86442832590 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 605099828131) ^ 5551374570 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 605099828131) ^ 4007283630 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 605099828131) ^ 3456390 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_730877766449 : Nat.Prime 730877766449 := by
  apply lucas_primality 730877766449 (3 : ZMod 730877766449)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (347, 1), (131642249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (347, 1), (131642249, 1)] : List FactorBlock).map factorBlockValue).prod) = 730877766449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_347
      · exact prime_eightyFiveCE_131642249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 730877766449) ^ 365438883224 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 730877766449) ^ 2106275984 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 730877766449) ^ 5552 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_822740544601 : Nat.Prime 822740544601 := by
  apply lucas_primality 822740544601 (14 : ZMod 822740544601)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (13, 1), (105479557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (13, 1), (105479557, 1)] : List FactorBlock).map factorBlockValue).prod) = 822740544601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_105479557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 822740544601) ^ 411370272300 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 822740544601) ^ 274246848200 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 822740544601) ^ 164548108920 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 822740544601) ^ 63287734200 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 822740544601) ^ 7800 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1143148907393 : Nat.Prime 1143148907393 := by
  apply lucas_primality 1143148907393 (3 : ZMod 1143148907393)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (17, 1), (19, 2), (37, 2), (1063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (17, 1), (19, 2), (37, 2), (1063, 1)] : List FactorBlock).map factorBlockValue).prod) = 1143148907393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_17
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_37
      · exact prime_eightyFiveCE_1063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1143148907393) ^ 571574453696 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1143148907393) ^ 67244053376 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1143148907393) ^ 60165731968 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1143148907393) ^ 30895916416 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1143148907393) ^ 1075398784 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1703315948377 : Nat.Prime 1703315948377 := by
  apply lucas_primality 1703315948377 (5 : ZMod 1703315948377)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (157, 1), (4801, 1), (13451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (157, 1), (4801, 1), (13451, 1)] : List FactorBlock).map factorBlockValue).prod) = 1703315948377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_157
      · exact prime_eightyFiveCE_4801
      · exact prime_eightyFiveCE_13451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1703315948377) ^ 851657974188 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1703315948377) ^ 567771982792 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1703315948377) ^ 243330849768 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1703315948377) ^ 10849146168 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1703315948377) ^ 354783576 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1703315948377) ^ 126631176 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1734136175687 : Nat.Prime 1734136175687 := by
  apply lucas_primality 1734136175687 (5 : ZMod 1734136175687)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4139, 1), (209487337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4139, 1), (209487337, 1)] : List FactorBlock).map factorBlockValue).prod) = 1734136175687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_4139
      · exact prime_eightyFiveCE_209487337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1734136175687) ^ 867068087843 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1734136175687) ^ 418974674 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1734136175687) ^ 8278 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_2235423330991 : Nat.Prime 2235423330991 := by
  apply lucas_primality 2235423330991 (7 : ZMod 2235423330991)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (24838037011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (24838037011, 1)] : List FactorBlock).map factorBlockValue).prod) = 2235423330991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_24838037011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2235423330991) ^ 1117711665495 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2235423330991) ^ 745141110330 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2235423330991) ^ 447084666198 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2235423330991) ^ 90 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_2481386350379 : Nat.Prime 2481386350379 := by
  apply lucas_primality 2481386350379 (2 : ZMod 2481386350379)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (95437936553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (95437936553, 1)] : List FactorBlock).map factorBlockValue).prod) = 2481386350379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_95437936553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2481386350379) ^ 1240693175189 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2481386350379) ^ 190875873106 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2481386350379) ^ 26 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_2511847982737 : Nat.Prime 2511847982737 := by
  apply lucas_primality 2511847982737 (5 : ZMod 2511847982737)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5814462923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5814462923, 1)] : List FactorBlock).map factorBlockValue).prod) = 2511847982737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5814462923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2511847982737) ^ 1255923991368 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2511847982737) ^ 837282660912 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2511847982737) ^ 432 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_2518025433799 : Nat.Prime 2518025433799 := by
  apply lucas_primality 2518025433799 (6 : ZMod 2518025433799)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (1620350987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (1620350987, 1)] : List FactorBlock).map factorBlockValue).prod) = 2518025433799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_37
      · exact prime_eightyFiveCE_1620350987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2518025433799) ^ 1259012716899 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2518025433799) ^ 839341811266 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2518025433799) ^ 359717919114 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2518025433799) ^ 68054741454 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2518025433799) ^ 1554 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_2699407465627 : Nat.Prime 2699407465627 := by
  apply lucas_primality 2699407465627 (11 : ZMod 2699407465627)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (173, 1), (313, 1), (8308579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (173, 1), (313, 1), (8308579, 1)] : List FactorBlock).map factorBlockValue).prod) = 2699407465627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_173
      · exact prime_eightyFiveCE_313
      · exact prime_eightyFiveCE_8308579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2699407465627) ^ 1349703732813 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 2699407465627) ^ 899802488542 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 2699407465627) ^ 15603511362 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 2699407465627) ^ 8624305002 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 2699407465627) ^ 324894 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_3593143580387 : Nat.Prime 3593143580387 := by
  apply lucas_primality 3593143580387 (2 : ZMod 3593143580387)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71359, 1), (25176527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71359, 1), (25176527, 1)] : List FactorBlock).map factorBlockValue).prod) = 3593143580387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_71359
      · exact prime_eightyFiveCE_25176527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3593143580387) ^ 1796571790193 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3593143580387) ^ 50353054 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3593143580387) ^ 142718 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_3630235164161 : Nat.Prime 3630235164161 := by
  apply lucas_primality 3630235164161 (6 : ZMod 3630235164161)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (5, 1), (11, 1), (19, 1), (701, 1), (9679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (5, 1), (11, 1), (19, 1), (701, 1), (9679, 1)] : List FactorBlock).map factorBlockValue).prod) = 3630235164161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_701
      · exact prime_eightyFiveCE_9679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3630235164161) ^ 1815117582080 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 3630235164161) ^ 726047032832 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 3630235164161) ^ 330021378560 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 3630235164161) ^ 191065008640 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 3630235164161) ^ 5178652160 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 3630235164161) ^ 375063040 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_5345937539693 : Nat.Prime 5345937539693 := by
  apply lucas_primality 5345937539693 (2 : ZMod 5345937539693)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (653, 1), (107720189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (653, 1), (107720189, 1)] : List FactorBlock).map factorBlockValue).prod) = 5345937539693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_653
      · exact prime_eightyFiveCE_107720189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5345937539693) ^ 2672968769846 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5345937539693) ^ 281365133668 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5345937539693) ^ 8186734364 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5345937539693) ^ 49628 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_6337859383517 : Nat.Prime 6337859383517 := by
  apply lucas_primality 6337859383517 (2 : ZMod 6337859383517)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (389, 1), (66773351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (389, 1), (66773351, 1)] : List FactorBlock).map factorBlockValue).prod) = 6337859383517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_61
      · exact prime_eightyFiveCE_389
      · exact prime_eightyFiveCE_66773351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6337859383517) ^ 3168929691758 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6337859383517) ^ 103899334156 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6337859383517) ^ 16292697644 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6337859383517) ^ 94916 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_6387656332817 : Nat.Prime 6387656332817 := by
  apply lucas_primality 6387656332817 (3 : ZMod 6387656332817)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (431, 1), (2027, 1), (41543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (431, 1), (2027, 1), (41543, 1)] : List FactorBlock).map factorBlockValue).prod) = 6387656332817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_431
      · exact prime_eightyFiveCE_2027
      · exact prime_eightyFiveCE_41543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6387656332817) ^ 3193828166408 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6387656332817) ^ 580696030256 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6387656332817) ^ 14820548336 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6387656332817) ^ 3151285808 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6387656332817) ^ 153760112 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_6527077686457 : Nat.Prime 6527077686457 := by
  apply lucas_primality 6527077686457 (7 : ZMod 6527077686457)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23917, 1), (11371057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23917, 1), (11371057, 1)] : List FactorBlock).map factorBlockValue).prod) = 6527077686457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_23917
      · exact prime_eightyFiveCE_11371057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6527077686457) ^ 3263538843228 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6527077686457) ^ 2175692562152 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6527077686457) ^ 272905368 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6527077686457) ^ 574008 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_7101878672807 : Nat.Prime 7101878672807 := by
  apply lucas_primality 7101878672807 (5 : ZMod 7101878672807)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1523563, 1), (2330681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1523563, 1), (2330681, 1)] : List FactorBlock).map factorBlockValue).prod) = 7101878672807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_1523563
      · exact prime_eightyFiveCE_2330681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7101878672807) ^ 3550939336403 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7101878672807) ^ 4661362 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7101878672807) ^ 3047126 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_9847483886231 : Nat.Prime 9847483886231 := by
  apply lucas_primality 9847483886231 (17 : ZMod 9847483886231)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (33956840987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (33956840987, 1)] : List FactorBlock).map factorBlockValue).prod) = 9847483886231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_29
      · exact prime_eightyFiveCE_33956840987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 9847483886231) ^ 4923741943115 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (17 : ZMod 9847483886231) ^ 1969496777246 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (17 : ZMod 9847483886231) ^ 339568409870 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (17 : ZMod 9847483886231) ^ 290 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_11733130315211 : Nat.Prime 11733130315211 := by
  apply lucas_primality 11733130315211 (6 : ZMod 11733130315211)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (89, 1), (4621, 1), (46769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (89, 1), (4621, 1), (46769, 1)] : List FactorBlock).map factorBlockValue).prod) = 11733130315211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_61
      · exact prime_eightyFiveCE_89
      · exact prime_eightyFiveCE_4621
      · exact prime_eightyFiveCE_46769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 11733130315211) ^ 5866565157605 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 11733130315211) ^ 2346626063042 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 11733130315211) ^ 192346398610 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 11733130315211) ^ 131832924890 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 11733130315211) ^ 2539089010 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 11733130315211) ^ 250874090 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_13412539985947 : Nat.Prime 13412539985947 := by
  apply lucas_primality 13412539985947 (2 : ZMod 13412539985947)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2235423330991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2235423330991, 1)] : List FactorBlock).map factorBlockValue).prod) = 13412539985947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_2235423330991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13412539985947) ^ 6706269992973 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13412539985947) ^ 4470846661982 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13412539985947) ^ 6 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_13583763600149 : Nat.Prime 13583763600149 := by
  apply lucas_primality 13583763600149 (2 : ZMod 13583763600149)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (485134414291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (485134414291, 1)] : List FactorBlock).map factorBlockValue).prod) = 13583763600149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_485134414291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13583763600149) ^ 6791881800074 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13583763600149) ^ 1940537657164 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13583763600149) ^ 28 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_17058263229353 : Nat.Prime 17058263229353 := by
  apply lucas_primality 17058263229353 (3 : ZMod 17058263229353)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (139861, 1), (15245729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (139861, 1), (15245729, 1)] : List FactorBlock).map factorBlockValue).prod) = 17058263229353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_139861
      · exact prime_eightyFiveCE_15245729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 17058263229353) ^ 8529131614676 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 17058263229353) ^ 121965832 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 17058263229353) ^ 1118888 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_17251235437763 : Nat.Prime 17251235437763 := by
  apply lucas_primality 17251235437763 (2 : ZMod 17251235437763)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (397, 1), (587216129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (397, 1), (587216129, 1)] : List FactorBlock).map factorBlockValue).prod) = 17251235437763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_37
      · exact prime_eightyFiveCE_397
      · exact prime_eightyFiveCE_587216129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17251235437763) ^ 8625617718881 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17251235437763) ^ 466249606426 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17251235437763) ^ 43453993546 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17251235437763) ^ 29378 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_19921457635901 : Nat.Prime 19921457635901 := by
  apply lucas_primality 19921457635901 (3 : ZMod 19921457635901)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (156019, 1), (1276861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (156019, 1), (1276861, 1)] : List FactorBlock).map factorBlockValue).prod) = 19921457635901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_156019
      · exact prime_eightyFiveCE_1276861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 19921457635901) ^ 9960728817950 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 19921457635901) ^ 3984291527180 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 19921457635901) ^ 127686100 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 19921457635901) ^ 15601900 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_22588249509853 : Nat.Prime 22588249509853 := by
  apply lucas_primality 22588249509853 (5 : ZMod 22588249509853)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (37, 1), (463, 1), (8452307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (37, 1), (463, 1), (8452307, 1)] : List FactorBlock).map factorBlockValue).prod) = 22588249509853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_37
      · exact prime_eightyFiveCE_463
      · exact prime_eightyFiveCE_8452307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 22588249509853) ^ 11294124754926 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 22588249509853) ^ 7529416503284 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 22588249509853) ^ 1737557654604 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 22588249509853) ^ 610493229996 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 22588249509853) ^ 48786716004 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 22588249509853) ^ 2672436 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_25256326076011 : Nat.Prime 25256326076011 := by
  apply lucas_primality 25256326076011 (2 : ZMod 25256326076011)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (19, 1), (14769781331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (19, 1), (14769781331, 1)] : List FactorBlock).map factorBlockValue).prod) = 25256326076011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_14769781331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25256326076011) ^ 12628163038005 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 25256326076011) ^ 8418775358670 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 25256326076011) ^ 5051265215202 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 25256326076011) ^ 1329280319790 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 25256326076011) ^ 1710 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_25966721345711 : Nat.Prime 25966721345711 := by
  apply lucas_primality 25966721345711 (11 : ZMod 25966721345711)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (655643, 1), (3960497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (655643, 1), (3960497, 1)] : List FactorBlock).map factorBlockValue).prod) = 25966721345711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_655643
      · exact prime_eightyFiveCE_3960497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 25966721345711) ^ 12983360672855 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 25966721345711) ^ 5193344269142 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 25966721345711) ^ 39604970 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 25966721345711) ^ 6556430 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_26994074656271 : Nat.Prime 26994074656271 := by
  apply lucas_primality 26994074656271 (7 : ZMod 26994074656271)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2699407465627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2699407465627, 1)] : List FactorBlock).map factorBlockValue).prod) = 26994074656271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_2699407465627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 26994074656271) ^ 13497037328135 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 26994074656271) ^ 5398814931254 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 26994074656271) ^ 10 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_28788222105647 : Nat.Prime 28788222105647 := by
  apply lucas_primality 28788222105647 (5 : ZMod 28788222105647)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2551, 1), (3677, 1), (1534549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2551, 1), (3677, 1), (1534549, 1)] : List FactorBlock).map factorBlockValue).prod) = 28788222105647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_2551
      · exact prime_eightyFiveCE_3677
      · exact prime_eightyFiveCE_1534549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 28788222105647) ^ 14394111052823 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 28788222105647) ^ 11285073346 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 28788222105647) ^ 7829268998 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 28788222105647) ^ 18760054 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_29894105208413 : Nat.Prime 29894105208413 := by
  apply lucas_primality 29894105208413 (2 : ZMod 29894105208413)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (673, 1), (1759, 1), (6313129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (673, 1), (1759, 1), (6313129, 1)] : List FactorBlock).map factorBlockValue).prod) = 29894105208413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_673
      · exact prime_eightyFiveCE_1759
      · exact prime_eightyFiveCE_6313129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 29894105208413) ^ 14947052604206 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 29894105208413) ^ 44419175644 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 29894105208413) ^ 16994943268 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 29894105208413) ^ 4735228 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_42769728422507 : Nat.Prime 42769728422507 := by
  apply lucas_primality 42769728422507 (2 : ZMod 42769728422507)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (281, 1), (1303, 1), (1424531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (281, 1), (1303, 1), (1424531, 1)] : List FactorBlock).map factorBlockValue).prod) = 42769728422507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_41
      · exact prime_eightyFiveCE_281
      · exact prime_eightyFiveCE_1303
      · exact prime_eightyFiveCE_1424531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42769728422507) ^ 21384864211253 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 42769728422507) ^ 1043164107866 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 42769728422507) ^ 152205439226 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 42769728422507) ^ 32824043302 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 42769728422507) ^ 30023726 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_54726886668217 : Nat.Prime 54726886668217 := by
  apply lucas_primality 54726886668217 (10 : ZMod 54726886668217)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (10883, 1), (29932489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (10883, 1), (29932489, 1)] : List FactorBlock).map factorBlockValue).prod) = 54726886668217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_10883
      · exact prime_eightyFiveCE_29932489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 54726886668217) ^ 27363443334108 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 54726886668217) ^ 18242295556072 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 54726886668217) ^ 7818126666888 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 54726886668217) ^ 5028658152 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 54726886668217) ^ 1828344 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_55292152064551 : Nat.Prime 55292152064551 := by
  apply lucas_primality 55292152064551 (15 : ZMod 55292152064551)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (211, 1), (14081, 1), (124067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (211, 1), (14081, 1), (124067, 1)] : List FactorBlock).map factorBlockValue).prod) = 55292152064551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_211
      · exact prime_eightyFiveCE_14081
      · exact prime_eightyFiveCE_124067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 55292152064551) ^ 27646076032275 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (15 : ZMod 55292152064551) ^ 18430717354850 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (15 : ZMod 55292152064551) ^ 11058430412910 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (15 : ZMod 55292152064551) ^ 262048114050 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (15 : ZMod 55292152064551) ^ 3926720550 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (15 : ZMod 55292152064551) ^ 445663650 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_55396559543579 : Nat.Prime 55396559543579 := by
  apply lucas_primality 55396559543579 (2 : ZMod 55396559543579)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2518025433799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2518025433799, 1)] : List FactorBlock).map factorBlockValue).prod) = 55396559543579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_2518025433799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55396559543579) ^ 27698279771789 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 55396559543579) ^ 5036050867598 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 55396559543579) ^ 22 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_55472863864039 : Nat.Prime 55472863864039 := by
  apply lucas_primality 55472863864039 (3 : ZMod 55472863864039)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (199889, 1), (1594933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (199889, 1), (1594933, 1)] : List FactorBlock).map factorBlockValue).prod) = 55472863864039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_29
      · exact prime_eightyFiveCE_199889
      · exact prime_eightyFiveCE_1594933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 55472863864039) ^ 27736431932019 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 55472863864039) ^ 18490954621346 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 55472863864039) ^ 1912857374622 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 55472863864039) ^ 277518342 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 55472863864039) ^ 34780686 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_56855611033831 : Nat.Prime 56855611033831 := by
  apply lucas_primality 56855611033831 (3 : ZMod 56855611033831)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (90247001641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (90247001641, 1)] : List FactorBlock).map factorBlockValue).prod) = 56855611033831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_90247001641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 56855611033831) ^ 28427805516915 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 56855611033831) ^ 18951870344610 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 56855611033831) ^ 11371122206766 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 56855611033831) ^ 8122230147690 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 56855611033831) ^ 630 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_65565302825383 : Nat.Prime 65565302825383 := by
  apply lucas_primality 65565302825383 (3 : ZMod 65565302825383)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (691, 1), (1439, 1), (477811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (691, 1), (1439, 1), (477811, 1)] : List FactorBlock).map factorBlockValue).prod) = 65565302825383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_23
      · exact prime_eightyFiveCE_691
      · exact prime_eightyFiveCE_1439
      · exact prime_eightyFiveCE_477811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65565302825383) ^ 32782651412691 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 65565302825383) ^ 21855100941794 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 65565302825383) ^ 2850665340234 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 65565302825383) ^ 94884664002 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 65565302825383) ^ 45563101338 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 65565302825383) ^ 137220162 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_88373352879991 : Nat.Prime 88373352879991 := by
  apply lucas_primality 88373352879991 (3 : ZMod 88373352879991)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (107693, 1), (9117827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (107693, 1), (9117827, 1)] : List FactorBlock).map factorBlockValue).prod) = 88373352879991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_107693
      · exact prime_eightyFiveCE_9117827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88373352879991) ^ 44186676439995 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 88373352879991) ^ 29457784293330 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 88373352879991) ^ 17674670575998 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 88373352879991) ^ 820604430 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 88373352879991) ^ 9692370 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_125518589559751 : Nat.Prime 125518589559751 := by
  apply lucas_primality 125518589559751 (3 : ZMod 125518589559751)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (7121, 1), (23502053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (7121, 1), (23502053, 1)] : List FactorBlock).map factorBlockValue).prod) = 125518589559751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_7121
      · exact prime_eightyFiveCE_23502053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 125518589559751) ^ 62759294779875 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 125518589559751) ^ 41839529853250 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 125518589559751) ^ 25103717911950 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 125518589559751) ^ 17626539750 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 125518589559751) ^ 5340750 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_158956349261581 : Nat.Prime 158956349261581 := by
  apply lucas_primality 158956349261581 (2 : ZMod 158956349261581)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (13, 1), (73, 1), (930548819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (13, 1), (73, 1), (930548819, 1)] : List FactorBlock).map factorBlockValue).prod) = 158956349261581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_73
      · exact prime_eightyFiveCE_930548819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 158956349261581) ^ 79478174630790 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 158956349261581) ^ 52985449753860 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 158956349261581) ^ 31791269852316 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 158956349261581) ^ 12227411481660 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 158956349261581) ^ 2177484236460 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 158956349261581) ^ 170820 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_175645853633069 : Nat.Prime 175645853633069 := by
  apply lucas_primality 175645853633069 (2 : ZMod 175645853633069)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (23, 1), (1279, 1), (16403561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (23, 1), (1279, 1), (16403561, 1)] : List FactorBlock).map factorBlockValue).prod) = 175645853633069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_23
      · exact prime_eightyFiveCE_1279
      · exact prime_eightyFiveCE_16403561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 175645853633069) ^ 87822926816534 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 175645853633069) ^ 25092264804724 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 175645853633069) ^ 13511219510236 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 175645853633069) ^ 7636776244916 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 175645853633069) ^ 137330612692 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 175645853633069) ^ 10707788 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_205766803330741 : Nat.Prime 205766803330741 := by
  apply lucas_primality 205766803330741 (10 : ZMod 205766803330741)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (1143148907393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (1143148907393, 1)] : List FactorBlock).map factorBlockValue).prod) = 205766803330741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_1143148907393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 205766803330741) ^ 102883401665370 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 205766803330741) ^ 68588934443580 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 205766803330741) ^ 41153360666148 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 205766803330741) ^ 180 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_210398000156431 : Nat.Prime 210398000156431 := by
  apply lucas_primality 210398000156431 (3 : ZMod 210398000156431)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (241836781789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (241836781789, 1)] : List FactorBlock).map factorBlockValue).prod) = 210398000156431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_29
      · exact prime_eightyFiveCE_241836781789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 210398000156431) ^ 105199000078215 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 210398000156431) ^ 70132666718810 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 210398000156431) ^ 42079600031286 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 210398000156431) ^ 7255103453670 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 210398000156431) ^ 870 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_240182684029447 : Nat.Prime 240182684029447 := by
  apply lucas_primality 240182684029447 (5 : ZMod 240182684029447)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2177531, 1), (18383411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2177531, 1), (18383411, 1)] : List FactorBlock).map factorBlockValue).prod) = 240182684029447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_2177531
      · exact prime_eightyFiveCE_18383411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 240182684029447) ^ 120091342014723 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 240182684029447) ^ 80060894676482 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 240182684029447) ^ 110300466 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 240182684029447) ^ 13065186 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_280246910379019 : Nat.Prime 280246910379019 := by
  apply lucas_primality 280246910379019 (2 : ZMod 280246910379019)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (641, 1), (6624282853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (641, 1), (6624282853, 1)] : List FactorBlock).map factorBlockValue).prod) = 280246910379019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_641
      · exact prime_eightyFiveCE_6624282853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 280246910379019) ^ 140123455189509 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 280246910379019) ^ 93415636793006 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 280246910379019) ^ 25476991852638 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 280246910379019) ^ 437202668298 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 280246910379019) ^ 42306 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_295292330842967 : Nat.Prime 295292330842967 := by
  apply lucas_primality 295292330842967 (5 : ZMod 295292330842967)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1956611, 1), (3971587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1956611, 1), (3971587, 1)] : List FactorBlock).map factorBlockValue).prod) = 295292330842967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_1956611
      · exact prime_eightyFiveCE_3971587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 295292330842967) ^ 147646165421483 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 295292330842967) ^ 15541701623314 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 295292330842967) ^ 150920306 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 295292330842967) ^ 74351218 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_331752912387307 : Nat.Prime 331752912387307 := by
  apply lucas_primality 331752912387307 (2 : ZMod 331752912387307)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (55292152064551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (55292152064551, 1)] : List FactorBlock).map factorBlockValue).prod) = 331752912387307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_55292152064551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 331752912387307) ^ 165876456193653 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 331752912387307) ^ 110584304129102 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 331752912387307) ^ 6 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_554994874327373 : Nat.Prime 554994874327373 := by
  apply lucas_primality 554994874327373 (2 : ZMod 554994874327373)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (1003019, 1), (1224169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (1003019, 1), (1224169, 1)] : List FactorBlock).map factorBlockValue).prod) = 554994874327373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_113
      · exact prime_eightyFiveCE_1003019
      · exact prime_eightyFiveCE_1224169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 554994874327373) ^ 277497437163686 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 554994874327373) ^ 4911459064844 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 554994874327373) ^ 553324388 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 554994874327373) ^ 453364588 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_663151909256971 : Nat.Prime 663151909256971 := by
  apply lucas_primality 663151909256971 (2 : ZMod 663151909256971)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (439, 1), (12113, 1), (593851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (439, 1), (12113, 1), (593851, 1)] : List FactorBlock).map factorBlockValue).prod) = 663151909256971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_439
      · exact prime_eightyFiveCE_12113
      · exact prime_eightyFiveCE_593851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 663151909256971) ^ 331575954628485 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 663151909256971) ^ 221050636418990 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 663151909256971) ^ 132630381851394 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 663151909256971) ^ 94735987036710 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 663151909256971) ^ 1510596604230 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 663151909256971) ^ 54747123690 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 663151909256971) ^ 1116697470 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_733523234408047 : Nat.Prime 733523234408047 := by
  apply lucas_primality 733523234408047 (3 : ZMod 733523234408047)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13583763600149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13583763600149, 1)] : List FactorBlock).map factorBlockValue).prod) = 733523234408047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_13583763600149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 733523234408047) ^ 366761617204023 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 733523234408047) ^ 244507744802682 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 733523234408047) ^ 54 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_808811583097337 : Nat.Prime 808811583097337 := by
  apply lucas_primality 808811583097337 (5 : ZMod 808811583097337)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13, 1), (23, 1), (6521, 1), (7407539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13, 1), (23, 1), (6521, 1), (7407539, 1)] : List FactorBlock).map factorBlockValue).prod) = 808811583097337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_23
      · exact prime_eightyFiveCE_6521
      · exact prime_eightyFiveCE_7407539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 808811583097337) ^ 404405791548668 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 808811583097337) ^ 115544511871048 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 808811583097337) ^ 62216275622872 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 808811583097337) ^ 35165721004232 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 808811583097337) ^ 124031833016 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 808811583097337) ^ 109187624 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_949478537474587 : Nat.Prime 949478537474587 := by
  apply lucas_primality 949478537474587 (2 : ZMod 949478537474587)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (2511847982737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (2511847982737, 1)] : List FactorBlock).map factorBlockValue).prod) = 949478537474587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_2511847982737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 949478537474587) ^ 474739268737293 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 949478537474587) ^ 316492845824862 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 949478537474587) ^ 135639791067798 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 949478537474587) ^ 378 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_985083960027907 : Nat.Prime 985083960027907 := by
  apply lucas_primality 985083960027907 (2 : ZMod 985083960027907)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (54726886668217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (54726886668217, 1)] : List FactorBlock).map factorBlockValue).prod) = 985083960027907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_54726886668217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 985083960027907) ^ 492541980013953 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 985083960027907) ^ 328361320009302 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 985083960027907) ^ 18 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1149481380495781 : Nat.Prime 1149481380495781 := by
  apply lucas_primality 1149481380495781 (2 : ZMod 1149481380495781)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (281, 1), (22726005941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (281, 1), (22726005941, 1)] : List FactorBlock).map factorBlockValue).prod) = 1149481380495781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_281
      · exact prime_eightyFiveCE_22726005941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1149481380495781) ^ 574740690247890 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1149481380495781) ^ 383160460165260 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1149481380495781) ^ 229896276099156 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1149481380495781) ^ 4090681069380 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1149481380495781) ^ 50580 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1242195702779639 : Nat.Prime 1242195702779639 := by
  apply lucas_primality 1242195702779639 (11 : ZMod 1242195702779639)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (43, 1), (4273, 1), (146970727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (43, 1), (4273, 1), (146970727, 1)] : List FactorBlock).map factorBlockValue).prod) = 1242195702779639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_23
      · exact prime_eightyFiveCE_43
      · exact prime_eightyFiveCE_4273
      · exact prime_eightyFiveCE_146970727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1242195702779639) ^ 621097851389819 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1242195702779639) ^ 54008508816506 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1242195702779639) ^ 28888272157666 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1242195702779639) ^ 290708098006 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1242195702779639) ^ 8451994 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1397323728191407 : Nat.Prime 1397323728191407 := by
  apply lucas_primality 1397323728191407 (3 : ZMod 1397323728191407)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9958709, 1), (23385289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9958709, 1), (23385289, 1)] : List FactorBlock).map factorBlockValue).prod) = 1397323728191407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_9958709
      · exact prime_eightyFiveCE_23385289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1397323728191407) ^ 698661864095703 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1397323728191407) ^ 465774576063802 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1397323728191407) ^ 140311734 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1397323728191407) ^ 59752254 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1615431701973599 : Nat.Prime 1615431701973599 := by
  apply lucas_primality 1615431701973599 (11 : ZMod 1615431701973599)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (2609, 1), (6586984913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (2609, 1), (6586984913, 1)] : List FactorBlock).map factorBlockValue).prod) = 1615431701973599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_47
      · exact prime_eightyFiveCE_2609
      · exact prime_eightyFiveCE_6586984913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1615431701973599) ^ 807715850986799 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1615431701973599) ^ 34370887276034 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1615431701973599) ^ 619176581822 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1615431701973599) ^ 245246 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1915898806702607 : Nat.Prime 1915898806702607 := by
  apply lucas_primality 1915898806702607 (5 : ZMod 1915898806702607)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (293, 1), (389, 1), (11411, 1), (66959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (293, 1), (389, 1), (11411, 1), (66959, 1)] : List FactorBlock).map factorBlockValue).prod) = 1915898806702607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_293
      · exact prime_eightyFiveCE_389
      · exact prime_eightyFiveCE_11411
      · exact prime_eightyFiveCE_66959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1915898806702607) ^ 957949403351303 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1915898806702607) ^ 174172618791146 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1915898806702607) ^ 6538903777142 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1915898806702607) ^ 4925189734454 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1915898806702607) ^ 167899290746 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1915898806702607) ^ 28613014034 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1947918857540399 : Nat.Prime 1947918857540399 := by
  apply lucas_primality 1947918857540399 (7 : ZMod 1947918857540399)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (503, 1), (28813, 1), (67202341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (503, 1), (28813, 1), (67202341, 1)] : List FactorBlock).map factorBlockValue).prod) = 1947918857540399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_503
      · exact prime_eightyFiveCE_28813
      · exact prime_eightyFiveCE_67202341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1947918857540399) ^ 973959428770199 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1947918857540399) ^ 3872602102466 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1947918857540399) ^ 67605555046 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1947918857540399) ^ 28985878 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_2171117201865517 : Nat.Prime 2171117201865517 := by
  apply lucas_primality 2171117201865517 (2 : ZMod 2171117201865517)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (60353, 1), (999267827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (60353, 1), (999267827, 1)] : List FactorBlock).map factorBlockValue).prod) = 2171117201865517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_60353
      · exact prime_eightyFiveCE_999267827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2171117201865517) ^ 1085558600932758 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2171117201865517) ^ 723705733955172 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2171117201865517) ^ 35973641772 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2171117201865517) ^ 2172708 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_2695831033713737 : Nat.Prime 2695831033713737 := by
  apply lucas_primality 2695831033713737 (3 : ZMod 2695831033713737)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (1019, 1), (19452685979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (1019, 1), (19452685979, 1)] : List FactorBlock).map factorBlockValue).prod) = 2695831033713737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_17
      · exact prime_eightyFiveCE_1019
      · exact prime_eightyFiveCE_19452685979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2695831033713737) ^ 1347915516856868 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2695831033713737) ^ 158578296100808 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2695831033713737) ^ 2645565293144 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2695831033713737) ^ 138584 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_2956491773759213 : Nat.Prime 2956491773759213 := by
  apply lucas_primality 2956491773759213 (2 : ZMod 2956491773759213)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (56855611033831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (56855611033831, 1)] : List FactorBlock).map factorBlockValue).prod) = 2956491773759213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_56855611033831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2956491773759213) ^ 1478245886879606 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2956491773759213) ^ 227422444135324 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2956491773759213) ^ 52 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_5044444386822343 : Nat.Prime 5044444386822343 := by
  apply lucas_primality 5044444386822343 (3 : ZMod 5044444386822343)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (280246910379019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (280246910379019, 1)] : List FactorBlock).map factorBlockValue).prod) = 5044444386822343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_280246910379019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5044444386822343) ^ 2522222193411171 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5044444386822343) ^ 1681481462274114 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5044444386822343) ^ 18 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_5892751134659723 : Nat.Prime 5892751134659723 := by
  apply lucas_primality 5892751134659723 (2 : ZMod 5892751134659723)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 1), (43, 1), (7499, 1), (28288751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 1), (43, 1), (7499, 1), (28288751, 1)] : List FactorBlock).map factorBlockValue).prod) = 5892751134659723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_17
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_43
      · exact prime_eightyFiveCE_7499
      · exact prime_eightyFiveCE_28288751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5892751134659723) ^ 2946375567329861 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5892751134659723) ^ 346632419685866 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5892751134659723) ^ 310144796561038 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5892751134659723) ^ 137040724061854 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5892751134659723) ^ 785804925278 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5892751134659723) ^ 208307222 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_6236668886685031 : Nat.Prime 6236668886685031 := by
  apply lucas_primality 6236668886685031 (7 : ZMod 6236668886685031)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (2803, 1), (8240732663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (2803, 1), (8240732663, 1)] : List FactorBlock).map factorBlockValue).prod) = 6236668886685031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_2803
      · exact prime_eightyFiveCE_8240732663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6236668886685031) ^ 3118334443342515 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6236668886685031) ^ 2078889628895010 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6236668886685031) ^ 1247333777337006 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6236668886685031) ^ 2224997819010 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6236668886685031) ^ 756810 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_6787136249982769 : Nat.Prime 6787136249982769 := by
  apply lucas_primality 6787136249982769 (11 : ZMod 6787136249982769)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (1206539, 1), (2725433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (1206539, 1), (2725433, 1)] : List FactorBlock).map factorBlockValue).prod) = 6787136249982769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_43
      · exact prime_eightyFiveCE_1206539
      · exact prime_eightyFiveCE_2725433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 6787136249982769) ^ 3393568124991384 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 6787136249982769) ^ 2262378749994256 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 6787136249982769) ^ 157840377906576 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 6787136249982769) ^ 5625293712 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 6787136249982769) ^ 2490296496 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_7034820083254343 : Nat.Prime 7034820083254343 := by
  apply lucas_primality 7034820083254343 (5 : ZMod 7034820083254343)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (523, 1), (761, 1), (8837647057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (523, 1), (761, 1), (8837647057, 1)] : List FactorBlock).map factorBlockValue).prod) = 7034820083254343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_523
      · exact prime_eightyFiveCE_761
      · exact prime_eightyFiveCE_8837647057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7034820083254343) ^ 3517410041627171 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7034820083254343) ^ 13450898820754 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7034820083254343) ^ 9244178821622 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7034820083254343) ^ 796006 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_7445061541393393 : Nat.Prime 7445061541393393 := by
  apply lucas_primality 7445061541393393 (5 : ZMod 7445061541393393)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 2), (29, 1), (1151, 1), (7243, 1), (13093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 2), (29, 1), (1151, 1), (7243, 1), (13093, 1)] : List FactorBlock).map factorBlockValue).prod) = 7445061541393393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_29
      · exact prime_eightyFiveCE_1151
      · exact prime_eightyFiveCE_7243
      · exact prime_eightyFiveCE_13093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7445061541393393) ^ 3722530770696696 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7445061541393393) ^ 2481687180464464 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7445061541393393) ^ 1063580220199056 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7445061541393393) ^ 256726260048048 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7445061541393393) ^ 6468341912592 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7445061541393393) ^ 1027897492944 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7445061541393393) ^ 568629156144 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_9013068554209919 : Nat.Prime 9013068554209919 := by
  apply lucas_primality 9013068554209919 (11 : ZMod 9013068554209919)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (563, 1), (3733, 1), (194932211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (563, 1), (3733, 1), (194932211, 1)] : List FactorBlock).map factorBlockValue).prod) = 9013068554209919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_563
      · exact prime_eightyFiveCE_3733
      · exact prime_eightyFiveCE_194932211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 9013068554209919) ^ 4506534277104959 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 9013068554209919) ^ 819369868564538 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 9013068554209919) ^ 16009002760586 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 9013068554209919) ^ 2414430365446 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 9013068554209919) ^ 46236938 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_9875512914298783 : Nat.Prime 9875512914298783 := by
  apply lucas_primality 9875512914298783 (6 : ZMod 9875512914298783)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (677, 1), (8011, 1), (2784239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (677, 1), (8011, 1), (2784239, 1)] : List FactorBlock).map factorBlockValue).prod) = 9875512914298783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_109
      · exact prime_eightyFiveCE_677
      · exact prime_eightyFiveCE_8011
      · exact prime_eightyFiveCE_2784239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9875512914298783) ^ 4937756457149391 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 9875512914298783) ^ 3291837638099594 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 9875512914298783) ^ 90601035910998 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 9875512914298783) ^ 14587168263366 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 9875512914298783) ^ 1232744091162 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 9875512914298783) ^ 3546934338 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_12067284266216369 : Nat.Prime 12067284266216369 := by
  apply lucas_primality 12067284266216369 (3 : ZMod 12067284266216369)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (17, 1), (6337859383517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (17, 1), (6337859383517, 1)] : List FactorBlock).map factorBlockValue).prod) = 12067284266216369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_17
      · exact prime_eightyFiveCE_6337859383517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12067284266216369) ^ 6033642133108184 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12067284266216369) ^ 1723897752316624 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12067284266216369) ^ 709840250953904 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12067284266216369) ^ 1904 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_13623380208299999 : Nat.Prime 13623380208299999 := by
  apply lucas_primality 13623380208299999 (7 : ZMod 13623380208299999)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (3739, 1), (6719, 1), (5115863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (3739, 1), (6719, 1), (5115863, 1)] : List FactorBlock).map factorBlockValue).prod) = 13623380208299999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_53
      · exact prime_eightyFiveCE_3739
      · exact prime_eightyFiveCE_6719
      · exact prime_eightyFiveCE_5115863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 13623380208299999) ^ 6811690104149999 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 13623380208299999) ^ 257044909590566 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 13623380208299999) ^ 3643589250682 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 13623380208299999) ^ 2027590446242 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 13623380208299999) ^ 2662968146 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_14069640166508687 : Nat.Prime 14069640166508687 := by
  apply lucas_primality 14069640166508687 (5 : ZMod 14069640166508687)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7034820083254343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7034820083254343, 1)] : List FactorBlock).map factorBlockValue).prod) = 14069640166508687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_7034820083254343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 14069640166508687) ^ 7034820083254343 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 14069640166508687) ^ 2 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_17336916213161453 : Nat.Prime 17336916213161453 := by
  apply lucas_primality 17336916213161453 (2 : ZMod 17336916213161453)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13337, 1), (324977810099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13337, 1), (324977810099, 1)] : List FactorBlock).map factorBlockValue).prod) = 17336916213161453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_13337
      · exact prime_eightyFiveCE_324977810099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 17336916213161453) ^ 8668458106580726 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17336916213161453) ^ 1299911240396 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17336916213161453) ^ 53348 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_22270084925757733 : Nat.Prime 22270084925757733 := by
  apply lucas_primality 22270084925757733 (2 : ZMod 22270084925757733)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (88373352879991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (88373352879991, 1)] : List FactorBlock).map factorBlockValue).prod) = 22270084925757733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_88373352879991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22270084925757733) ^ 11135042462878866 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 22270084925757733) ^ 7423361641919244 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 22270084925757733) ^ 3181440703679676 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 22270084925757733) ^ 252 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_23481538830843559 : Nat.Prime 23481538830843559 := by
  apply lucas_primality 23481538830843559 (3 : ZMod 23481538830843559)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (313, 1), (6689, 1), (1869260249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (313, 1), (6689, 1), (1869260249, 1)] : List FactorBlock).map factorBlockValue).prod) = 23481538830843559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_313
      · exact prime_eightyFiveCE_6689
      · exact prime_eightyFiveCE_1869260249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23481538830843559) ^ 11740769415421779 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23481538830843559) ^ 7827179610281186 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23481538830843559) ^ 75020890833366 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23481538830843559) ^ 3510470747622 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23481538830843559) ^ 12561942 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_28222371991449403 : Nat.Prime 28222371991449403 := by
  apply lucas_primality 28222371991449403 (2 : ZMod 28222371991449403)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (79, 1), (35149, 1), (130304329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (79, 1), (35149, 1), (130304329, 1)] : List FactorBlock).map factorBlockValue).prod) = 28222371991449403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_79
      · exact prime_eightyFiveCE_35149
      · exact prime_eightyFiveCE_130304329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28222371991449403) ^ 14111185995724701 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28222371991449403) ^ 9407457330483134 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28222371991449403) ^ 2170951691649954 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28222371991449403) ^ 357245215081638 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28222371991449403) ^ 802935275298 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28222371991449403) ^ 216588138 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_34253910377784173 : Nat.Prime 34253910377784173 := by
  apply lucas_primality 34253910377784173 (2 : ZMod 34253910377784173)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (295292330842967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (295292330842967, 1)] : List FactorBlock).map factorBlockValue).prod) = 34253910377784173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_29
      · exact prime_eightyFiveCE_295292330842967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 34253910377784173) ^ 17126955188892086 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 34253910377784173) ^ 1181169323371868 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 34253910377784173) ^ 116 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_34484441414873431 : Nat.Prime 34484441414873431 := by
  apply lucas_primality 34484441414873431 (3 : ZMod 34484441414873431)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1149481380495781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1149481380495781, 1)] : List FactorBlock).map factorBlockValue).prod) = 34484441414873431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_1149481380495781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 34484441414873431) ^ 17242220707436715 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 34484441414873431) ^ 11494813804957810 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 34484441414873431) ^ 6896888282974686 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 34484441414873431) ^ 30 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_40817333031825653 : Nat.Prime 40817333031825653 := by
  apply lucas_primality 40817333031825653 (2 : ZMod 40817333031825653)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (271273, 1), (37616472181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (271273, 1), (37616472181, 1)] : List FactorBlock).map factorBlockValue).prod) = 40817333031825653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_271273
      · exact prime_eightyFiveCE_37616472181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 40817333031825653) ^ 20408666515912826 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 40817333031825653) ^ 150465888724 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 40817333031825653) ^ 1085092 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_68507820755568347 : Nat.Prime 68507820755568347 := by
  apply lucas_primality 68507820755568347 (2 : ZMod 68507820755568347)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (34253910377784173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (34253910377784173, 1)] : List FactorBlock).map factorBlockValue).prod) = 68507820755568347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_34253910377784173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 68507820755568347) ^ 34253910377784173 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 68507820755568347) ^ 2 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_89619296915413453 : Nat.Prime 89619296915413453 := by
  apply lucas_primality 89619296915413453 (2 : ZMod 89619296915413453)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (127, 1), (5345937539693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (127, 1), (5345937539693, 1)] : List FactorBlock).map factorBlockValue).prod) = 89619296915413453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_127
      · exact prime_eightyFiveCE_5345937539693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 89619296915413453) ^ 44809648457706726 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 89619296915413453) ^ 29873098971804484 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 89619296915413453) ^ 8147208810492132 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 89619296915413453) ^ 705663755239476 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 89619296915413453) ^ 16764 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_91019159389689173 : Nat.Prime 91019159389689173 := by
  apply lucas_primality 91019159389689173 (2 : ZMod 91019159389689173)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (554994874327373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (554994874327373, 1)] : List FactorBlock).map factorBlockValue).prod) = 91019159389689173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_41
      · exact prime_eightyFiveCE_554994874327373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 91019159389689173) ^ 45509579694844586 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 91019159389689173) ^ 2219979497309492 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 91019159389689173) ^ 164 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_130579049920791179 : Nat.Prime 130579049920791179 := by
  apply lucas_primality 130579049920791179 (2 : ZMod 130579049920791179)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (41, 1), (47, 1), (443, 1), (461, 1), (23700587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (41, 1), (47, 1), (443, 1), (461, 1), (23700587, 1)] : List FactorBlock).map factorBlockValue).prod) = 130579049920791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_41
      · exact prime_eightyFiveCE_47
      · exact prime_eightyFiveCE_443
      · exact prime_eightyFiveCE_461
      · exact prime_eightyFiveCE_23700587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 130579049920791179) ^ 65289524960395589 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 130579049920791179) ^ 18654149988684454 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 130579049920791179) ^ 3184854876116858 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 130579049920791179) ^ 2778277657889174 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 130579049920791179) ^ 294760835035646 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 130579049920791179) ^ 283251735186098 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 130579049920791179) ^ 5509528094 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_168246878918205707 : Nat.Prime 168246878918205707 := by
  apply lucas_primality 168246878918205707 (2 : ZMod 168246878918205707)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23173, 1), (3630235164161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23173, 1), (3630235164161, 1)] : List FactorBlock).map factorBlockValue).prod) = 168246878918205707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_23173
      · exact prime_eightyFiveCE_3630235164161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 168246878918205707) ^ 84123439459102853 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 168246878918205707) ^ 7260470328322 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 168246878918205707) ^ 46346 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_308064534289350473 : Nat.Prime 308064534289350473 := by
  apply lucas_primality 308064534289350473 (3 : ZMod 308064534289350473)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (1242195702779639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (1242195702779639, 1)] : List FactorBlock).map factorBlockValue).prod) = 308064534289350473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_31
      · exact prime_eightyFiveCE_1242195702779639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 308064534289350473) ^ 154032267144675236 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 308064534289350473) ^ 9937565622237112 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 308064534289350473) ^ 248 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_867288915112689593 : Nat.Prime 867288915112689593 := by
  apply lucas_primality 867288915112689593 (3 : ZMod 867288915112689593)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (57403627, 1), (1888576037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (57403627, 1), (1888576037, 1)] : List FactorBlock).map factorBlockValue).prod) = 867288915112689593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_57403627
      · exact prime_eightyFiveCE_1888576037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 867288915112689593) ^ 433644457556344796 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 867288915112689593) ^ 15108608296 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 867288915112689593) ^ 459229016 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1041602992859426741 : Nat.Prime 1041602992859426741 := by
  apply lucas_primality 1041602992859426741 (2 : ZMod 1041602992859426741)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (71, 1), (733523234408047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (71, 1), (733523234408047, 1)] : List FactorBlock).map factorBlockValue).prod) = 1041602992859426741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_71
      · exact prime_eightyFiveCE_733523234408047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1041602992859426741) ^ 520801496429713370 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1041602992859426741) ^ 208320598571885348 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1041602992859426741) ^ 14670464688160940 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1041602992859426741) ^ 1420 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1229900577883832609 : Nat.Prime 1229900577883832609 := by
  apply lucas_primality 1229900577883832609 (3 : ZMod 1229900577883832609)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (2956491773759213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (2956491773759213, 1)] : List FactorBlock).map factorBlockValue).prod) = 1229900577883832609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_2956491773759213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1229900577883832609) ^ 614950288941916304 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1229900577883832609) ^ 94607736760294816 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1229900577883832609) ^ 416 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1233140773600230247 : Nat.Prime 1233140773600230247 := by
  apply lucas_primality 1233140773600230247 (3 : ZMod 1233140773600230247)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (68507820755568347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (68507820755568347, 1)] : List FactorBlock).map factorBlockValue).prod) = 1233140773600230247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_68507820755568347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1233140773600230247) ^ 616570386800115123 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1233140773600230247) ^ 411046924533410082 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1233140773600230247) ^ 18 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1641898525284274151 : Nat.Prime 1641898525284274151 := by
  apply lucas_primality 1641898525284274151 (11 : ZMod 1641898525284274151)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1860533, 1), (17649765151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1860533, 1), (17649765151, 1)] : List FactorBlock).map factorBlockValue).prod) = 1641898525284274151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_1860533
      · exact prime_eightyFiveCE_17649765151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1641898525284274151) ^ 820949262642137075 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1641898525284274151) ^ 328379705056854830 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1641898525284274151) ^ 882488257550 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1641898525284274151) ^ 93026650 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_2459801155767665219 : Nat.Prime 2459801155767665219 := by
  apply lucas_primality 2459801155767665219 (2 : ZMod 2459801155767665219)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1229900577883832609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1229900577883832609, 1)] : List FactorBlock).map factorBlockValue).prod) = 2459801155767665219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_1229900577883832609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2459801155767665219) ^ 1229900577883832609 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2459801155767665219) ^ 2 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_2536006193731104373 : Nat.Prime 2536006193731104373 := by
  apply lucas_primality 2536006193731104373 (2 : ZMod 2536006193731104373)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (23481538830843559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (23481538830843559, 1)] : List FactorBlock).map factorBlockValue).prod) = 2536006193731104373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_23481538830843559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2536006193731104373) ^ 1268003096865552186 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2536006193731104373) ^ 845335397910368124 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2536006193731104373) ^ 108 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_3138402544041485207 : Nat.Prime 3138402544041485207 := by
  apply lucas_primality 3138402544041485207 (5 : ZMod 3138402544041485207)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (34534271, 1), (45438957493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (34534271, 1), (45438957493, 1)] : List FactorBlock).map factorBlockValue).prod) = 3138402544041485207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_34534271
      · exact prime_eightyFiveCE_45438957493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3138402544041485207) ^ 1569201272020742603 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 3138402544041485207) ^ 90877914986 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 3138402544041485207) ^ 69068542 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_7429433243596965817 : Nat.Prime 7429433243596965817 := by
  apply lucas_primality 7429433243596965817 (5 : ZMod 7429433243596965817)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (157, 1), (383, 1), (2917, 1), (1764857267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (157, 1), (383, 1), (2917, 1), (1764857267, 1)] : List FactorBlock).map factorBlockValue).prod) = 7429433243596965817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_157
      · exact prime_eightyFiveCE_383
      · exact prime_eightyFiveCE_2917
      · exact prime_eightyFiveCE_1764857267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7429433243596965817) ^ 3714716621798482908 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7429433243596965817) ^ 2476477747865655272 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7429433243596965817) ^ 47321230850936088 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7429433243596965817) ^ 19397998025057352 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7429433243596965817) ^ 2546943175727448 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7429433243596965817) ^ 4209651048 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_7959824050445415859 : Nat.Prime 7959824050445415859 := by
  apply lucas_primality 7959824050445415859 (2 : ZMod 7959824050445415859)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (127, 1), (381037, 1), (1442871803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (127, 1), (381037, 1), (1442871803, 1)] : List FactorBlock).map factorBlockValue).prod) = 7959824050445415859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_127
      · exact prime_eightyFiveCE_381037
      · exact prime_eightyFiveCE_1442871803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7959824050445415859) ^ 3979912025222707929 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7959824050445415859) ^ 2653274683481805286 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7959824050445415859) ^ 418938107918179782 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7959824050445415859) ^ 62675779924767054 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7959824050445415859) ^ 20889897963834 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7959824050445415859) ^ 5516653686 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_9788244058801428071 : Nat.Prime 9788244058801428071 := by
  apply lucas_primality 9788244058801428071 (13 : ZMod 9788244058801428071)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (14929, 1), (65565302825383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (14929, 1), (65565302825383, 1)] : List FactorBlock).map factorBlockValue).prod) = 9788244058801428071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_14929
      · exact prime_eightyFiveCE_65565302825383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 9788244058801428071) ^ 4894122029400714035 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (13 : ZMod 9788244058801428071) ^ 1957648811760285614 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (13 : ZMod 9788244058801428071) ^ 655653028253830 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (13 : ZMod 9788244058801428071) ^ 149290 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_16990177888898223941 : Nat.Prime 16990177888898223941 := by
  apply lucas_primality 16990177888898223941 (2 : ZMod 16990177888898223941)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (17336916213161453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (17336916213161453, 1)] : List FactorBlock).map factorBlockValue).prod) = 16990177888898223941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_17336916213161453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16990177888898223941) ^ 8495088944449111970 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 16990177888898223941) ^ 3398035577779644788 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 16990177888898223941) ^ 2427168269842603420 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 16990177888898223941) ^ 980 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_17753367593730783731 : Nat.Prime 17753367593730783731 := by
  apply lucas_primality 17753367593730783731 (2 : ZMod 17753367593730783731)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (89, 1), (85369, 1), (233663320853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (89, 1), (85369, 1), (233663320853, 1)] : List FactorBlock).map factorBlockValue).prod) = 17753367593730783731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_89
      · exact prime_eightyFiveCE_85369
      · exact prime_eightyFiveCE_233663320853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17753367593730783731) ^ 8876683796865391865 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17753367593730783731) ^ 3550673518746156746 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17753367593730783731) ^ 199476040378997570 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17753367593730783731) ^ 207960355559170 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17753367593730783731) ^ 75978410 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_24931797254773465531 : Nat.Prime 24931797254773465531 := by
  apply lucas_primality 24931797254773465531 (3 : ZMod 24931797254773465531)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (13291, 1), (18127, 1), (93228139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (13291, 1), (18127, 1), (93228139, 1)] : List FactorBlock).map factorBlockValue).prod) = 24931797254773465531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_37
      · exact prime_eightyFiveCE_13291
      · exact prime_eightyFiveCE_18127
      · exact prime_eightyFiveCE_93228139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 24931797254773465531) ^ 12465898627386732765 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 24931797254773465531) ^ 8310599084924488510 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 24931797254773465531) ^ 4986359450954693106 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 24931797254773465531) ^ 673832358237120690 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 24931797254773465531) ^ 1875840587974830 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 24931797254773465531) ^ 1375395666948390 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 24931797254773465531) ^ 267427812270 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_26583006869076501707 : Nat.Prime 26583006869076501707 := by
  apply lucas_primality 26583006869076501707 (2 : ZMod 26583006869076501707)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (168246878918205707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (168246878918205707, 1)] : List FactorBlock).map factorBlockValue).prod) = 26583006869076501707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_79
      · exact prime_eightyFiveCE_168246878918205707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26583006869076501707) ^ 13291503434538250853 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 26583006869076501707) ^ 336493757836411414 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 26583006869076501707) ^ 158 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_28407396999858614359 : Nat.Prime 28407396999858614359 := by
  apply lucas_primality 28407396999858614359 (6 : ZMod 28407396999858614359)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (4813, 1), (42769728422507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (4813, 1), (42769728422507, 1)] : List FactorBlock).map factorBlockValue).prod) = 28407396999858614359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_23
      · exact prime_eightyFiveCE_4813
      · exact prime_eightyFiveCE_42769728422507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 28407396999858614359) ^ 14203698499929307179 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 28407396999858614359) ^ 9469132333286204786 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 28407396999858614359) ^ 1235104217385157146 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 28407396999858614359) ^ 5902222522305966 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 28407396999858614359) ^ 664194 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_55458716933738039219 : Nat.Prime 55458716933738039219 := by
  apply lucas_primality 55458716933738039219 (2 : ZMod 55458716933738039219)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3709, 1), (2412959, 1), (281669849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3709, 1), (2412959, 1), (281669849, 1)] : List FactorBlock).map factorBlockValue).prod) = 55458716933738039219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_3709
      · exact prime_eightyFiveCE_2412959
      · exact prime_eightyFiveCE_281669849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 55458716933738039219) ^ 27729358466869019609 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 55458716933738039219) ^ 5041701539430730838 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 55458716933738039219) ^ 14952471537810202 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 55458716933738039219) ^ 22983696338702 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 55458716933738039219) ^ 196892628482 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_60825866492667998003 : Nat.Prime 60825866492667998003 := by
  apply lucas_primality 60825866492667998003 (2 : ZMod 60825866492667998003)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (16073, 1), (23859811, 1), (79303867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (16073, 1), (23859811, 1), (79303867, 1)] : List FactorBlock).map factorBlockValue).prod) = 60825866492667998003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_16073
      · exact prime_eightyFiveCE_23859811
      · exact prime_eightyFiveCE_79303867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 60825866492667998003) ^ 30412933246333999001 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 60825866492667998003) ^ 3784350556378274 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 60825866492667998003) ^ 2549302108582 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 60825866492667998003) ^ 766997484406 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_94208599618626238307 : Nat.Prime 94208599618626238307 := by
  apply lucas_primality 94208599618626238307 (2 : ZMod 94208599618626238307)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (512637481, 1), (8353289083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (512637481, 1), (8353289083, 1)] : List FactorBlock).map factorBlockValue).prod) = 94208599618626238307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_512637481
      · exact prime_eightyFiveCE_8353289083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 94208599618626238307) ^ 47104299809313119153 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94208599618626238307) ^ 8564418147147839846 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94208599618626238307) ^ 183772359826 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94208599618626238307) ^ 11278024582 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_99546287247600221209 : Nat.Prime 99546287247600221209 := by
  apply lucas_primality 99546287247600221209 (7 : ZMod 99546287247600221209)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (277, 1), (457, 1), (677, 1), (1459, 1), (3823, 1), (8677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (277, 1), (457, 1), (677, 1), (1459, 1), (3823, 1), (8677, 1)] : List FactorBlock).map factorBlockValue).prod) = 99546287247600221209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_277
      · exact prime_eightyFiveCE_457
      · exact prime_eightyFiveCE_677
      · exact prime_eightyFiveCE_1459
      · exact prime_eightyFiveCE_3823
      · exact prime_eightyFiveCE_8677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 99546287247600221209) ^ 49773143623800110604 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 99546287247600221209) ^ 33182095749200073736 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 99546287247600221209) ^ 359372878150181304 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 99546287247600221209) ^ 217825573845952344 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 99546287247600221209) ^ 147040306126440504 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 99546287247600221209) ^ 68229120800274312 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 99546287247600221209) ^ 26038788189275496 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (7 : ZMod 99546287247600221209) ^ 11472431398824504 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_115238565952609423529 : Nat.Prime 115238565952609423529 := by
  apply lucas_primality 115238565952609423529 (3 : ZMod 115238565952609423529)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (137, 1), (409, 1), (43117, 1), (5962322281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (137, 1), (409, 1), (43117, 1), (5962322281, 1)] : List FactorBlock).map factorBlockValue).prod) = 115238565952609423529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_137
      · exact prime_eightyFiveCE_409
      · exact prime_eightyFiveCE_43117
      · exact prime_eightyFiveCE_5962322281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 115238565952609423529) ^ 57619282976304711764 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 115238565952609423529) ^ 841157415712477544 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 115238565952609423529) ^ 281756884969705192 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 115238565952609423529) ^ 2672694434970184 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 115238565952609423529) ^ 19327798888 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_230477131905218847059 : Nat.Prime 230477131905218847059 := by
  apply lucas_primality 230477131905218847059 (2 : ZMod 230477131905218847059)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (115238565952609423529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (115238565952609423529, 1)] : List FactorBlock).map factorBlockValue).prod) = 230477131905218847059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_115238565952609423529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 230477131905218847059) ^ 115238565952609423529 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 230477131905218847059) ^ 2 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_404470173740875521017 : Nat.Prime 404470173740875521017 := by
  apply lucas_primality 404470173740875521017 (3 : ZMod 404470173740875521017)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (1233140773600230247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (1233140773600230247, 1)] : List FactorBlock).map factorBlockValue).prod) = 404470173740875521017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_41
      · exact prime_eightyFiveCE_1233140773600230247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 404470173740875521017) ^ 202235086870437760508 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 404470173740875521017) ^ 9865126188801841976 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 404470173740875521017) ^ 328 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_836638540178934816497 : Nat.Prime 836638540178934816497 := by
  apply lucas_primality 836638540178934816497 (3 : ZMod 836638540178934816497)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (32369, 1), (1615431701973599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (32369, 1), (1615431701973599, 1)] : List FactorBlock).map factorBlockValue).prod) = 836638540178934816497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_32369
      · exact prime_eightyFiveCE_1615431701973599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 836638540178934816497) ^ 418319270089467408248 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 836638540178934816497) ^ 25846907231577584 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 836638540178934816497) ^ 517904 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1063714523848203374353 : Nat.Prime 1063714523848203374353 := by
  apply lucas_primality 1063714523848203374353 (5 : ZMod 1063714523848203374353)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (11813, 1), (10461611, 1), (19924277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (11813, 1), (10461611, 1), (19924277, 1)] : List FactorBlock).map factorBlockValue).prod) = 1063714523848203374353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_11813
      · exact prime_eightyFiveCE_10461611
      · exact prime_eightyFiveCE_19924277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1063714523848203374353) ^ 531857261924101687176 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1063714523848203374353) ^ 354571507949401124784 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1063714523848203374353) ^ 90046095305866704 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1063714523848203374353) ^ 101677889174832 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1063714523848203374353) ^ 53387860640976 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1494134613764700867917 : Nat.Prime 1494134613764700867917 := by
  apply lucas_primality 1494134613764700867917 (2 : ZMod 1494134613764700867917)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (71, 1), (709, 1), (97553, 1), (6914994467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (71, 1), (709, 1), (97553, 1), (6914994467, 1)] : List FactorBlock).map factorBlockValue).prod) = 1494134613764700867917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_71
      · exact prime_eightyFiveCE_709
      · exact prime_eightyFiveCE_97553
      · exact prime_eightyFiveCE_6914994467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1494134613764700867917) ^ 747067306882350433958 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1494134613764700867917) ^ 135830419433154624356 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1494134613764700867917) ^ 21044149489643674196 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1494134613764700867917) ^ 2107383094167420124 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1494134613764700867917) ^ 15316131884869772 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1494134613764700867917) ^ 216071700548 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_2319174694700888639467 : Nat.Prime 2319174694700888639467 := by
  apply lucas_primality 2319174694700888639467 (5 : ZMod 2319174694700888639467)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (199, 1), (8087, 1), (240182684029447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (199, 1), (8087, 1), (240182684029447, 1)] : List FactorBlock).map factorBlockValue).prod) = 2319174694700888639467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_199
      · exact prime_eightyFiveCE_8087
      · exact prime_eightyFiveCE_240182684029447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2319174694700888639467) ^ 1159587347350444319733 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2319174694700888639467) ^ 773058231566962879822 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2319174694700888639467) ^ 11654144194476827334 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2319174694700888639467) ^ 286778124731159718 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2319174694700888639467) ^ 9655878 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_2971802173126313942341 : Nat.Prime 2971802173126313942341 := by
  apply lucas_primality 2971802173126313942341 (2 : ZMod 2971802173126313942341)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (61, 1), (225977, 1), (3593143580387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (61, 1), (225977, 1), (3593143580387, 1)] : List FactorBlock).map factorBlockValue).prod) = 2971802173126313942341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_61
      · exact prime_eightyFiveCE_225977
      · exact prime_eightyFiveCE_3593143580387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2971802173126313942341) ^ 1485901086563156971170 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2971802173126313942341) ^ 990600724375437980780 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2971802173126313942341) ^ 594360434625262788468 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2971802173126313942341) ^ 48718068411906785940 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2971802173126313942341) ^ 13150905504216420 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2971802173126313942341) ^ 827075820 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_3226679846673063858827 : Nat.Prime 3226679846673063858827 := by
  apply lucas_primality 3226679846673063858827 (2 : ZMod 3226679846673063858827)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (230477131905218847059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (230477131905218847059, 1)] : List FactorBlock).map factorBlockValue).prod) = 3226679846673063858827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_230477131905218847059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3226679846673063858827) ^ 1613339923336531929413 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3226679846673063858827) ^ 460954263810437694118 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3226679846673063858827) ^ 14 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_4519387318446927568307 : Nat.Prime 4519387318446927568307 := by
  apply lucas_primality 4519387318446927568307 (2 : ZMod 4519387318446927568307)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (16990177888898223941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (16990177888898223941, 1)] : List FactorBlock).map factorBlockValue).prod) = 4519387318446927568307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_16990177888898223941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4519387318446927568307) ^ 2259693659223463784153 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4519387318446927568307) ^ 645626759778132509758 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4519387318446927568307) ^ 237862490444575135174 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4519387318446927568307) ^ 266 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_7127391007609125479119 : Nat.Prime 7127391007609125479119 := by
  apply lucas_primality 7127391007609125479119 (3 : ZMod 7127391007609125479119)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (331, 1), (13339, 1), (29894105208413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (331, 1), (13339, 1), (29894105208413, 1)] : List FactorBlock).map factorBlockValue).prod) = 7127391007609125479119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_331
      · exact prime_eightyFiveCE_13339
      · exact prime_eightyFiveCE_29894105208413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7127391007609125479119) ^ 3563695503804562739559 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7127391007609125479119) ^ 2375797002536375159706 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7127391007609125479119) ^ 21532903346251134378 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7127391007609125479119) ^ 534327236495173962 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7127391007609125479119) ^ 238421286 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_10013717813891114040779 : Nat.Prime 10013717813891114040779 := by
  apply lucas_primality 10013717813891114040779 (2 : ZMod 10013717813891114040779)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (251, 1), (867288915112689593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (251, 1), (867288915112689593, 1)] : List FactorBlock).map factorBlockValue).prod) = 10013717813891114040779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_23
      · exact prime_eightyFiveCE_251
      · exact prime_eightyFiveCE_867288915112689593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10013717813891114040779) ^ 5006858906945557020389 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10013717813891114040779) ^ 435379035386570175686 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10013717813891114040779) ^ 39895290095183721278 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10013717813891114040779) ^ 11546 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_12783003238436251768249 : Nat.Prime 12783003238436251768249 := by
  apply lucas_primality 12783003238436251768249 (31 : ZMod 12783003238436251768249)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (683, 1), (4127, 1), (26994074656271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (683, 1), (4127, 1), (26994074656271, 1)] : List FactorBlock).map factorBlockValue).prod) = 12783003238436251768249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_683
      · exact prime_eightyFiveCE_4127
      · exact prime_eightyFiveCE_26994074656271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 12783003238436251768249) ^ 6391501619218125884124 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (31 : ZMod 12783003238436251768249) ^ 4261001079478750589416 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (31 : ZMod 12783003238436251768249) ^ 1826143319776607395464 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (31 : ZMod 12783003238436251768249) ^ 18715963745880310056 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (31 : ZMod 12783003238436251768249) ^ 3097408102359159624 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (31 : ZMod 12783003238436251768249) ^ 473548488 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_13779084918350566360031 : Nat.Prime 13779084918350566360031 := by
  apply lucas_primality 13779084918350566360031 (13 : ZMod 13779084918350566360031)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (191, 1), (12659, 1), (808229, 1), (37110737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (191, 1), (12659, 1), (808229, 1), (37110737, 1)] : List FactorBlock).map factorBlockValue).prod) = 13779084918350566360031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_191
      · exact prime_eightyFiveCE_12659
      · exact prime_eightyFiveCE_808229
      · exact prime_eightyFiveCE_37110737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 13779084918350566360031) ^ 6889542459175283180015 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (13 : ZMod 13779084918350566360031) ^ 2755816983670113272006 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (13 : ZMod 13779084918350566360031) ^ 725214995702661387370 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (13 : ZMod 13779084918350566360031) ^ 72141805855238567330 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (13 : ZMod 13779084918350566360031) ^ 1088481311189712170 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (13 : ZMod 13779084918350566360031) ^ 17048491106296070 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (13 : ZMod 13779084918350566360031) ^ 371296450360190 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_15330128236130434066187 : Nat.Prime 15330128236130434066187 := by
  apply lucas_primality 15330128236130434066187 (5 : ZMod 15330128236130434066187)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (99546287247600221209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (99546287247600221209, 1)] : List FactorBlock).map factorBlockValue).prod) = 15330128236130434066187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_99546287247600221209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15330128236130434066187) ^ 7665064118065217033093 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 15330128236130434066187) ^ 2190018319447204866598 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 15330128236130434066187) ^ 1393648021466403096926 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 15330128236130434066187) ^ 154 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_23536405658690227286527 : Nat.Prime 23536405658690227286527 := by
  apply lucas_primality 23536405658690227286527 (3 : ZMod 23536405658690227286527)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (701, 1), (1334239, 1), (62598285517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (701, 1), (1334239, 1), (62598285517, 1)] : List FactorBlock).map factorBlockValue).prod) = 23536405658690227286527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_67
      · exact prime_eightyFiveCE_701
      · exact prime_eightyFiveCE_1334239
      · exact prime_eightyFiveCE_62598285517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23536405658690227286527) ^ 11768202829345113643263 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23536405658690227286527) ^ 7845468552896742428842 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23536405658690227286527) ^ 351289636696869063978 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23536405658690227286527) ^ 33575471695706458326 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23536405658690227286527) ^ 17640322055261634 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23536405658690227286527) ^ 375991218678 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_30778657214350177805921 : Nat.Prime 30778657214350177805921 := by
  apply lucas_primality 30778657214350177805921 (3 : ZMod 30778657214350177805921)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (13, 1), (31, 1), (5036453, 1), (94776322793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (13, 1), (31, 1), (5036453, 1), (94776322793, 1)] : List FactorBlock).map factorBlockValue).prod) = 30778657214350177805921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_13
      · exact prime_eightyFiveCE_31
      · exact prime_eightyFiveCE_5036453
      · exact prime_eightyFiveCE_94776322793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30778657214350177805921) ^ 15389328607175088902960 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 30778657214350177805921) ^ 6155731442870035561184 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 30778657214350177805921) ^ 2367589016488475215840 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 30778657214350177805921) ^ 992859910140328316320 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 30778657214350177805921) ^ 6111177293692640 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 30778657214350177805921) ^ 324750489440 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_40797896521996093160137 : Nat.Prime 40797896521996093160137 := by
  apply lucas_primality 40797896521996093160137 (10 : ZMod 40797896521996093160137)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (283, 1), (14674963, 1), (14114486479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (283, 1), (14674963, 1), (14114486479, 1)] : List FactorBlock).map factorBlockValue).prod) = 40797896521996093160137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_29
      · exact prime_eightyFiveCE_283
      · exact prime_eightyFiveCE_14674963
      · exact prime_eightyFiveCE_14114486479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 40797896521996093160137) ^ 20398948260998046580068 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 40797896521996093160137) ^ 13599298840665364386712 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 40797896521996093160137) ^ 1406824017999865281384 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 40797896521996093160137) ^ 144162178522954392792 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 40797896521996093160137) ^ 2780102172795672 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 40797896521996093160137) ^ 2890498112184 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_65738466899247257910101 : Nat.Prime 65738466899247257910101 := by
  apply lucas_primality 65738466899247257910101 (3 : ZMod 65738466899247257910101)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (877, 1), (43451, 1), (17251235437763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (877, 1), (43451, 1), (17251235437763, 1)] : List FactorBlock).map factorBlockValue).prod) = 65738466899247257910101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_877
      · exact prime_eightyFiveCE_43451
      · exact prime_eightyFiveCE_17251235437763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65738466899247257910101) ^ 32869233449623628955050 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 65738466899247257910101) ^ 13147693379849451582020 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 65738466899247257910101) ^ 74958343100624011300 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 65738466899247257910101) ^ 1512933347891815100 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 65738466899247257910101) ^ 3810652700 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_251113061950078344828233 : Nat.Prime 251113061950078344828233 := by
  apply lucas_primality 251113061950078344828233 (3 : ZMod 251113061950078344828233)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1259, 1), (24931797254773465531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1259, 1), (24931797254773465531, 1)] : List FactorBlock).map factorBlockValue).prod) = 251113061950078344828233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_1259
      · exact prime_eightyFiveCE_24931797254773465531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 251113061950078344828233) ^ 125556530975039172414116 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 251113061950078344828233) ^ 199454378038187724248 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 251113061950078344828233) ^ 10072 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_448227855257537478762113 : Nat.Prime 448227855257537478762113 := by
  apply lucas_primality 448227855257537478762113 (3 : ZMod 448227855257537478762113)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (79, 1), (487, 1), (91019159389689173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (79, 1), (487, 1), (91019159389689173, 1)] : List FactorBlock).map factorBlockValue).prod) = 448227855257537478762113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_79
      · exact prime_eightyFiveCE_487
      · exact prime_eightyFiveCE_91019159389689173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 448227855257537478762113) ^ 224113927628768739381056 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 448227855257537478762113) ^ 5673770319715664288128 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 448227855257537478762113) ^ 920385739748536917376 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 448227855257537478762113) ^ 4924544 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_490368487011559401065059 : Nat.Prime 490368487011559401065059 := by
  apply lucas_primality 490368487011559401065059 (2 : ZMod 490368487011559401065059)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (137, 1), (28407396999858614359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (137, 1), (28407396999858614359, 1)] : List FactorBlock).map factorBlockValue).prod) = 490368487011559401065059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_137
      · exact prime_eightyFiveCE_28407396999858614359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 490368487011559401065059) ^ 245184243505779700532529 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 490368487011559401065059) ^ 163456162337186467021686 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 490368487011559401065059) ^ 70052641001651343009294 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 490368487011559401065059) ^ 3579332021982185409234 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 490368487011559401065059) ^ 17262 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_608136215173285461996077 : Nat.Prime 608136215173285461996077 := by
  apply lucas_primality 608136215173285461996077 (2 : ZMod 608136215173285461996077)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (16433, 1), (11245043, 1), (822740544601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (16433, 1), (11245043, 1), (822740544601, 1)] : List FactorBlock).map factorBlockValue).prod) = 608136215173285461996077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_16433
      · exact prime_eightyFiveCE_11245043
      · exact prime_eightyFiveCE_822740544601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 608136215173285461996077) ^ 304068107586642730998038 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 608136215173285461996077) ^ 37007011207526651372 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 608136215173285461996077) ^ 54080381477712932 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 608136215173285461996077) ^ 739159166476 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_909419604611137379762047 : Nat.Prime 909419604611137379762047 := by
  apply lucas_primality 909419604611137379762047 (3 : ZMod 909419604611137379762047)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13779084918350566360031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13779084918350566360031, 1)] : List FactorBlock).map factorBlockValue).prod) = 909419604611137379762047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_11
      · exact prime_eightyFiveCE_13779084918350566360031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 909419604611137379762047) ^ 454709802305568689881023 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 909419604611137379762047) ^ 303139868203712459920682 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 909419604611137379762047) ^ 82674509510103398160186 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 909419604611137379762047) ^ 66 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1461541713673171161733409 : Nat.Prime 1461541713673171161733409 := by
  apply lucas_primality 1461541713673171161733409 (6 : ZMod 1461541713673171161733409)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (19, 1), (251, 1), (63040381, 1), (21702863803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (19, 1), (251, 1), (63040381, 1), (21702863803, 1)] : List FactorBlock).map factorBlockValue).prod) = 1461541713673171161733409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_251
      · exact prime_eightyFiveCE_63040381
      · exact prime_eightyFiveCE_21702863803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1461541713673171161733409) ^ 730770856836585580866704 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1461541713673171161733409) ^ 208791673381881594533344 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1461541713673171161733409) ^ 76923248088061640091232 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1461541713673171161733409) ^ 5822875353279566381408 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1461541713673171161733409) ^ 23184214474737568 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1461541713673171161733409) ^ 67343265245536 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_5456517627666824278572283 : Nat.Prime 5456517627666824278572283 := by
  apply lucas_primality 5456517627666824278572283 (3 : ZMod 5456517627666824278572283)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (909419604611137379762047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (909419604611137379762047, 1)] : List FactorBlock).map factorBlockValue).prod) = 5456517627666824278572283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_909419604611137379762047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5456517627666824278572283) ^ 2728258813833412139286141 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5456517627666824278572283) ^ 1818839209222274759524094 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5456517627666824278572283) ^ 6 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_31922708115864009764442737 : Nat.Prime 31922708115864009764442737 := by
  apply lucas_primality 31922708115864009764442737 (3 : ZMod 31922708115864009764442737)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (109, 1), (113, 1), (1367, 1), (6236668886685031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (109, 1), (113, 1), (1367, 1), (6236668886685031, 1)] : List FactorBlock).map factorBlockValue).prod) = 31922708115864009764442737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_109
      · exact prime_eightyFiveCE_113
      · exact prime_eightyFiveCE_1367
      · exact prime_eightyFiveCE_6236668886685031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 31922708115864009764442737) ^ 15961354057932004882221368 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 31922708115864009764442737) ^ 1680142532413895250760144 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 31922708115864009764442737) ^ 292868881796917520774704 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 31922708115864009764442737) ^ 282501841733309820924272 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 31922708115864009764442737) ^ 23352383405899056155408 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 31922708115864009764442737) ^ 5118551056 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_51455547951223708519439701 : Nat.Prime 51455547951223708519439701 := by
  apply lucas_primality 51455547951223708519439701 (2 : ZMod 51455547951223708519439701)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (122747857, 1), (1397323728191407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (122747857, 1), (1397323728191407, 1)] : List FactorBlock).map factorBlockValue).prod) = 51455547951223708519439701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_122747857
      · exact prime_eightyFiveCE_1397323728191407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51455547951223708519439701) ^ 25727773975611854259719850 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 51455547951223708519439701) ^ 17151849317074569506479900 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 51455547951223708519439701) ^ 10291109590244741703887940 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 51455547951223708519439701) ^ 419197118457422100 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 51455547951223708519439701) ^ 36824357100 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_68130633999145696771841177 : Nat.Prime 68130633999145696771841177 := by
  apply lucas_primality 68130633999145696771841177 (3 : ZMod 68130633999145696771841177)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (448227855257537478762113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (448227855257537478762113, 1)] : List FactorBlock).map factorBlockValue).prod) = 68130633999145696771841177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_448227855257537478762113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68130633999145696771841177) ^ 34065316999572848385920588 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 68130633999145696771841177) ^ 3585822842060299830096904 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 68130633999145696771841177) ^ 152 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_146064949344098695840793221 : Nat.Prime 146064949344098695840793221 := by
  apply lucas_primality 146064949344098695840793221 (14 : ZMod 146064949344098695840793221)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 3), (17, 1), (19, 1), (3823, 1), (1915898806702607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 3), (17, 1), (19, 1), (3823, 1), (1915898806702607, 1)] : List FactorBlock).map factorBlockValue).prod) = 146064949344098695840793221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_17
      · exact prime_eightyFiveCE_19
      · exact prime_eightyFiveCE_3823
      · exact prime_eightyFiveCE_1915898806702607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 146064949344098695840793221) ^ 73032474672049347920396610 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 146064949344098695840793221) ^ 48688316448032898613597740 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 146064949344098695840793221) ^ 29212989868819739168158644 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 146064949344098695840793221) ^ 20866421334871242262970460 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 146064949344098695840793221) ^ 8592055843770511520046660 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 146064949344098695840793221) ^ 7687628912847299781094380 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 146064949344098695840793221) ^ 38206892321239522846140 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (14 : ZMod 146064949344098695840793221) ^ 76238342460 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_162346825765331022194613467 : Nat.Prime 162346825765331022194613467 := by
  apply lucas_primality 162346825765331022194613467 (2 : ZMod 162346825765331022194613467)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3644953001, 1), (22270084925757733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3644953001, 1), (22270084925757733, 1)] : List FactorBlock).map factorBlockValue).prod) = 162346825765331022194613467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3644953001
      · exact prime_eightyFiveCE_22270084925757733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 162346825765331022194613467) ^ 81173412882665511097306733 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 162346825765331022194613467) ^ 44540169851515466 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 162346825765331022194613467) ^ 7289906002 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_168611887833456212648432443 : Nat.Prime 168611887833456212648432443 := by
  apply lucas_primality 168611887833456212648432443 (2 : ZMod 168611887833456212648432443)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1266899, 1), (34589473, 1), (213761627447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1266899, 1), (34589473, 1), (213761627447, 1)] : List FactorBlock).map factorBlockValue).prod) = 168611887833456212648432443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_1266899
      · exact prime_eightyFiveCE_34589473
      · exact prime_eightyFiveCE_213761627447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 168611887833456212648432443) ^ 84305943916728106324216221 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 168611887833456212648432443) ^ 56203962611152070882810814 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 168611887833456212648432443) ^ 133090236738253177758 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 168611887833456212648432443) ^ 4874659056917583354 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 168611887833456212648432443) ^ 788784637576086 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_1794512234798926834615459573 : Nat.Prime 1794512234798926834615459573 := by
  apply lucas_primality 1794512234798926834615459573 (2 : ZMod 1794512234798926834615459573)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (101, 1), (1453, 1), (5383459, 1), (6527077686457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (101, 1), (1453, 1), (5383459, 1), (6527077686457, 1)] : List FactorBlock).map factorBlockValue).prod) = 1794512234798926834615459573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_29
      · exact prime_eightyFiveCE_101
      · exact prime_eightyFiveCE_1453
      · exact prime_eightyFiveCE_5383459
      · exact prime_eightyFiveCE_6527077686457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1794512234798926834615459573) ^ 897256117399463417307729786 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1794512234798926834615459573) ^ 598170744932975611538486524 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1794512234798926834615459573) ^ 61879732234445752917774468 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1794512234798926834615459573) ^ 17767447869296305293222372 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1794512234798926834615459573) ^ 1235039390776962721689924 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1794512234798926834615459573) ^ 333338144638777194108 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1794512234798926834615459573) ^ 274933488002196 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_5911334420514111925792102121 : Nat.Prime 5911334420514111925792102121 := by
  apply lucas_primality 5911334420514111925792102121 (3 : ZMod 5911334420514111925792102121)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (98909, 1), (1494134613764700867917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (98909, 1), (1494134613764700867917, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111925792102121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_5
      · exact prime_eightyFiveCE_98909
      · exact prime_eightyFiveCE_1494134613764700867917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5911334420514111925792102121) ^ 2955667210257055962896051060 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5911334420514111925792102121) ^ 1182266884102822385158420424 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5911334420514111925792102121) ^ 59765384550588034716680 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5911334420514111925792102121) ^ 3956360 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_7178048939195707338461838287 : Nat.Prime 7178048939195707338461838287 := by
  apply lucas_primality 7178048939195707338461838287 (5 : ZMod 7178048939195707338461838287)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17058263229353, 1), (210398000156431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17058263229353, 1), (210398000156431, 1)] : List FactorBlock).map factorBlockValue).prod) = 7178048939195707338461838287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_17058263229353
      · exact prime_eightyFiveCE_210398000156431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7178048939195707338461838287) ^ 3589024469597853669230919143 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7178048939195707338461838287) ^ 420796000312862 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7178048939195707338461838287) ^ 34116526458706 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_14356097878391414676923676577 : Nat.Prime 14356097878391414676923676577 := by
  apply lucas_primality 14356097878391414676923676577 (5 : ZMod 14356097878391414676923676577)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (29, 1), (101, 1), (1453, 1), (5383459, 1), (6527077686457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (29, 1), (101, 1), (1453, 1), (5383459, 1), (6527077686457, 1)] : List FactorBlock).map factorBlockValue).prod) = 14356097878391414676923676577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_29
      · exact prime_eightyFiveCE_101
      · exact prime_eightyFiveCE_1453
      · exact prime_eightyFiveCE_5383459
      · exact prime_eightyFiveCE_6527077686457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 14356097878391414676923676577) ^ 7178048939195707338461838288 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 14356097878391414676923676577) ^ 4785365959463804892307892192 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 14356097878391414676923676577) ^ 495037857875566023342195744 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 14356097878391414676923676577) ^ 142139582954370442345778976 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 14356097878391414676923676577) ^ 9880315126215701773519392 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 14356097878391414676923676577) ^ 2666705157110217552864 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (5 : ZMod 14356097878391414676923676577) ^ 2199467904017568 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_20098537029747980547693147203 : Nat.Prime 20098537029747980547693147203 := by
  apply lucas_primality 20098537029747980547693147203 (2 : ZMod 20098537029747980547693147203)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20910521, 1), (5878998439, 1), (81745951279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20910521, 1), (5878998439, 1), (81745951279, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747980547693147203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_20910521
      · exact prime_eightyFiveCE_5878998439
      · exact prime_eightyFiveCE_81745951279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20098537029747980547693147203) ^ 10049268514873990273846573601 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 20098537029747980547693147203) ^ 961168639927622106962 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 20098537029747980547693147203) ^ 3418700861769012718 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 20098537029747980547693147203) ^ 245865840635353438 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_100492685148739902738465736033 : Nat.Prime 100492685148739902738465736033 := by
  apply lucas_primality 100492685148739902738465736033 (10 : ZMod 100492685148739902738465736033)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (29, 1), (101, 1), (1453, 1), (5383459, 1), (6527077686457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (29, 1), (101, 1), (1453, 1), (5383459, 1), (6527077686457, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_7
      · exact prime_eightyFiveCE_29
      · exact prime_eightyFiveCE_101
      · exact prime_eightyFiveCE_1453
      · exact prime_eightyFiveCE_5383459
      · exact prime_eightyFiveCE_6527077686457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 100492685148739902738465736033) ^ 50246342574369951369232868016 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 100492685148739902738465736033) ^ 33497561716246634246155245344 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 100492685148739902738465736033) ^ 14356097878391414676923676576 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 100492685148739902738465736033) ^ 3465265005128962163395370208 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 100492685148739902738465736033) ^ 994977080680593096420452832 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 100492685148739902738465736033) ^ 69162205883509912414635744 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 100492685148739902738465736033) ^ 18666936099771522870048 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (10 : ZMod 100492685148739902738465736033) ^ 15396275328122976 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem prime_eightyFiveCE_100492685148739902738465736099 : Nat.Prime 100492685148739902738465736099 := by
  apply lucas_primality 100492685148739902738465736099 (2 : ZMod 100492685148739902738465736099)
  · rw [← eightyFiveCEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (62814480863, 1), (9875512914298783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (62814480863, 1), (9875512914298783, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFiveCE_2
      · exact prime_eightyFiveCE_3
      · exact prime_eightyFiveCE_62814480863
      · exact prime_eightyFiveCE_9875512914298783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 100492685148739902738465736099) ^ 50246342574369951369232868049 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 100492685148739902738465736099) ^ 33497561716246634246155245366 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 100492685148739902738465736099) ^ 1599833092116402846 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide
    · change (2 : ZMod 100492685148739902738465736099) ^ 10175945899806 ≠ 1
      rw [← eightyFiveCEFastPow_eq_pow]
      decide

private theorem phi_eightyFiveCE_100492685148739902738465736000 : Nat.totient 100492685148739902738465736000 = 40184380364198698152043776000 := by
  rw [← show ((([(2, 6), (5, 3), (3259, 1), (111773, 1), (34484441414873431, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_5, prime_eightyFiveCE_3259, prime_eightyFiveCE_111773, prime_eightyFiveCE_34484441414873431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736001 : Nat.totient 100492685148739902738465736001 = 90454353072518244311112409920 := by
  rw [← show ((([(11, 2), (107, 2), (1949, 1), (37783, 1), (985083960027907, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_11, prime_eightyFiveCE_107, prime_eightyFiveCE_1949, prime_eightyFiveCE_37783, prime_eightyFiveCE_985083960027907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736002 : Nat.totient 100492685148739902738465736002 = 33229362501636408502019795520 := by
  rw [← show ((([(2, 1), (3, 1), (127, 1), (7487, 1), (1788736493, 1), (9847483886231, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_3, prime_eightyFiveCE_127, prime_eightyFiveCE_7487, prime_eightyFiveCE_1788736493, prime_eightyFiveCE_9847483886231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736003 : Nat.totient 100492685148739902738465736003 = 88881642126462314310386429952 := by
  rw [← show ((([(13, 1), (29, 1), (157, 1), (797, 1), (1250661883, 1), (1703315948377, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_13, prime_eightyFiveCE_29, prime_eightyFiveCE_157, prime_eightyFiveCE_797, prime_eightyFiveCE_1250661883, prime_eightyFiveCE_1703315948377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736004 : Nat.totient 100492685148739902738465736004 = 43068293635171514555610400320 := by
  rw [← show ((([(2, 2), (7, 1), (17058263229353, 1), (210398000156431, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_7, prime_eightyFiveCE_17058263229353, prime_eightyFiveCE_210398000156431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736005 : Nat.totient 100492685148739902738465736005 = 51841347433016184260538402816 := by
  rw [← show ((([(3, 1), (5, 1), (43, 1), (103, 1), (643213, 1), (101132699, 1), (23253648329, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_3, prime_eightyFiveCE_5, prime_eightyFiveCE_43, prime_eightyFiveCE_103, prime_eightyFiveCE_643213, prime_eightyFiveCE_101132699, prime_eightyFiveCE_23253648329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736006 : Nat.totient 100492685148739902738465736006 = 44801605287800057462739240960 := by
  rw [← show ((([(2, 1), (17, 1), (19, 1), (519703, 1), (46860311, 1), (6387656332817, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_17, prime_eightyFiveCE_19, prime_eightyFiveCE_519703, prime_eightyFiveCE_46860311, prime_eightyFiveCE_6387656332817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736007 : Nat.totient 100492685148739902738465736007 = 99077198006787152867054340000 := by
  rw [← show ((([(71, 1), (1041701, 1), (47197411, 1), (28788222105647, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_71, prime_eightyFiveCE_1041701, prime_eightyFiveCE_47197411, prime_eightyFiveCE_28788222105647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736008 : Nat.totient 100492685148739902738465736008 = 32006853675248419810367078400 := by
  rw [← show ((([(2, 3), (3, 2), (23, 1), (1871, 1), (2207, 1), (12097, 1), (2958947, 1), (410566141, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_3, prime_eightyFiveCE_23, prime_eightyFiveCE_1871, prime_eightyFiveCE_2207, prime_eightyFiveCE_12097, prime_eightyFiveCE_2958947, prime_eightyFiveCE_410566141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736009 : Nat.totient 100492685148739902738465736009 = 98135097963570683280420929424 := by
  rw [← show ((([(47, 1), (659, 1), (1399, 1), (2319174694700888639467, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_47, prime_eightyFiveCE_659, prime_eightyFiveCE_1399, prime_eightyFiveCE_2319174694700888639467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736010 : Nat.totient 100492685148739902738465736010 = 40197072129829548185916789120 := by
  rw [← show ((([(2, 1), (5, 1), (20910521, 1), (5878998439, 1), (81745951279, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_5, prime_eightyFiveCE_20910521, prime_eightyFiveCE_5878998439, prime_eightyFiveCE_81745951279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736011 : Nat.totient 100492685148739902738465736011 = 57358913302033656816351828384 := by
  rw [← show ((([(3, 1), (7, 1), (877, 1), (5456517627666824278572283, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_3, prime_eightyFiveCE_7, prime_eightyFiveCE_877, prime_eightyFiveCE_5456517627666824278572283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736012 : Nat.totient 100492685148739902738465736012 = 45678487835527026121766476800 := by
  rw [← show ((([(2, 2), (11, 1), (8602817, 1), (438746899, 1), (605099828131, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_11, prime_eightyFiveCE_8602817, prime_eightyFiveCE_438746899, prime_eightyFiveCE_605099828131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736013 : Nat.totient 100492685148739902738465736013 = 100491467801282073008470154320 := by
  rw [← show ((([(89387, 1), (1079339, 1), (1041602992859426741, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_89387, prime_eightyFiveCE_1079339, prime_eightyFiveCE_1041602992859426741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736014 : Nat.totient 100492685148739902738465736014 = 33490528421304087044995561632 := by
  rw [← show ((([(2, 1), (3, 1), (5237, 1), (52579, 1), (60825866492667998003, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_3, prime_eightyFiveCE_5237, prime_eightyFiveCE_52579, prime_eightyFiveCE_60825866492667998003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736015 : Nat.totient 100492685148739902738465736015 = 80394148118991922190772588808 := by
  rw [← show ((([(5, 1), (20098537029747980547693147203, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_5, prime_eightyFiveCE_20098537029747980547693147203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736016 : Nat.totient 100492685148739902738465736016 = 45594988970378671056959700480 := by
  rw [← show ((([(2, 4), (13, 1), (59, 1), (508619, 1), (1200371, 1), (13412539985947, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_13, prime_eightyFiveCE_59, prime_eightyFiveCE_508619, prime_eightyFiveCE_1200371, prime_eightyFiveCE_13412539985947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736017 : Nat.totient 100492685148739902738465736017 = 66840399762653238263298892800 := by
  rw [← show ((([(3, 5), (433, 1), (128283851, 1), (7445061541393393, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_3, prime_eightyFiveCE_433, prime_eightyFiveCE_128283851, prime_eightyFiveCE_7445061541393393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736018 : Nat.totient 100492685148739902738465736018 = 43068293635174244030771029716 := by
  rw [← show ((([(2, 1), (7, 1), (7178048939195707338461838287, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_7, prime_eightyFiveCE_7178048939195707338461838287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736019 : Nat.totient 100492685148739902738465736019 = 100492077012524729453003574696 := by
  rw [← show ((([(165247, 1), (608136215173285461996077, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_165247, prime_eightyFiveCE_608136215173285461996077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736020 : Nat.totient 100492685148739902738465736020 = 26603416143878452424093184000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (269, 1), (281, 1), (980939051, 1), (22588249509853, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_3, prime_eightyFiveCE_5, prime_eightyFiveCE_269, prime_eightyFiveCE_281, prime_eightyFiveCE_980939051, prime_eightyFiveCE_22588249509853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736021 : Nat.totient 100492685148739902738465736021 = 100492665714002152242031605120 := by
  rw [← show ((([(5207003, 1), (743240737, 1), (25966721345711, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_5207003, prime_eightyFiveCE_743240737, prime_eightyFiveCE_25966721345711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736022 : Nat.totient 100492685148739902738465736022 = 48581646562496209416018481920 := by
  rw [← show ((([(2, 1), (31, 1), (1109, 1), (1461541713673171161733409, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_31, prime_eightyFiveCE_1109, prime_eightyFiveCE_1461541713673171161733409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736023 : Nat.totient 100492685148739902738465736023 = 57321901313923670078887695360 := by
  rw [← show ((([(3, 1), (11, 1), (17, 1), (442879, 1), (404470173740875521017, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_3, prime_eightyFiveCE_11, prime_eightyFiveCE_17, prime_eightyFiveCE_442879, prime_eightyFiveCE_404470173740875521017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736024 : Nat.totient 100492685148739902738465736024 = 49610299622332536956845117440 := by
  rw [← show ((([(2, 3), (79, 1), (4005433, 1), (54315421, 1), (730877766449, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_79, prime_eightyFiveCE_4005433, prime_eightyFiveCE_54315421, prime_eightyFiveCE_730877766449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736025 : Nat.totient 100492685148739902738465736025 = 63675975018540459255496704000 := by
  rw [← show ((([(5, 2), (7, 1), (19, 1), (41, 1), (8681, 1), (10457, 1), (78697, 1), (103186742653, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_5, prime_eightyFiveCE_7, prime_eightyFiveCE_19, prime_eightyFiveCE_41, prime_eightyFiveCE_8681, prime_eightyFiveCE_10457, prime_eightyFiveCE_78697, prime_eightyFiveCE_103186742653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736026 : Nat.totient 100492685148739902738465736026 = 33491604277259605578480222528 := by
  rw [← show ((([(2, 1), (3, 2), (5623, 1), (168490633, 1), (5892751134659723, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_3, prime_eightyFiveCE_5623, prime_eightyFiveCE_168490633, prime_eightyFiveCE_5892751134659723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736027 : Nat.totient 100492685148739902738465736027 = 97423681384679719460304228480 := by
  rw [← show ((([(37, 1), (277, 1), (109408591, 1), (89619296915413453, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_37, prime_eightyFiveCE_277, prime_eightyFiveCE_109408591, prime_eightyFiveCE_89619296915413453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736028 : Nat.totient 100492685148739902738465736028 = 49909118798703038943936002832 := by
  rw [← show ((([(2, 2), (149, 1), (168611887833456212648432443, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_149, prime_eightyFiveCE_168611887833456212648432443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736029 : Nat.totient 100492685148739902738465736029 = 61440226419807173544039244800 := by
  rw [← show ((([(3, 1), (13, 1), (191, 1), (983, 1), (7789, 1), (8563, 1), (205766803330741, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_3, prime_eightyFiveCE_13, prime_eightyFiveCE_191, prime_eightyFiveCE_983, prime_eightyFiveCE_7789, prime_eightyFiveCE_8563, prime_eightyFiveCE_205766803330741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736030 : Nat.totient 100492685148739902738465736030 = 39448854816194087500438800000 := by
  rw [← show ((([(2, 1), (5, 1), (61, 1), (443, 1), (2962735211, 1), (125518589559751, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_5, prime_eightyFiveCE_61, prime_eightyFiveCE_443, prime_eightyFiveCE_2962735211, prime_eightyFiveCE_125518589559751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736031 : Nat.totient 100492685148739902738465736031 = 96121144903063177805922330624 := by
  rw [← show ((([(23, 1), (42139, 1), (10228643, 1), (44963297, 1), (225447913, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_23, prime_eightyFiveCE_42139, prime_eightyFiveCE_10228643, prime_eightyFiveCE_44963297, prime_eightyFiveCE_225447913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736032 : Nat.totient 100492685148739902738465736032 = 27428748184022417497733529600 := by
  rw [← show ((([(2, 5), (3, 1), (7, 1), (29, 1), (101, 1), (1453, 1), (5383459, 1), (6527077686457, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_3, prime_eightyFiveCE_7, prime_eightyFiveCE_29, prime_eightyFiveCE_101, prime_eightyFiveCE_1453, prime_eightyFiveCE_5383459, prime_eightyFiveCE_6527077686457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736033 : Nat.totient 100492685148739902738465736033 = 100492685148739902738465736032 := by
  rw [← show ((([(100492685148739902738465736033, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_100492685148739902738465736033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736034 : Nat.totient 100492685148739902738465736034 = 45441212989059909126346158720 := by
  rw [← show ((([(2, 1), (11, 1), (233, 1), (1103, 1), (10249369219, 1), (1734136175687, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_11, prime_eightyFiveCE_233, prime_eightyFiveCE_1103, prime_eightyFiveCE_10249369219, prime_eightyFiveCE_1734136175687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736035 : Nat.totient 100492685148739902738465736035 = 53596098670672953719775238272 := by
  rw [← show ((([(3, 2), (5, 1), (711562889, 1), (3138402544041485207, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_3, prime_eightyFiveCE_5, prime_eightyFiveCE_711562889, prime_eightyFiveCE_3138402544041485207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736036 : Nat.totient 100492685148739902738465736036 = 49938052280388767256689718912 := by
  rw [← show ((([(2, 2), (163, 1), (1636049, 1), (94208599618626238307, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_163, prime_eightyFiveCE_1636049, prime_eightyFiveCE_94208599618626238307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736037 : Nat.totient 100492685148739902738465736037 = 99937976394892179674739771360 := by
  rw [← show ((([(199, 1), (2011, 1), (251113061950078344828233, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_199, prime_eightyFiveCE_2011, prime_eightyFiveCE_251113061950078344828233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736038 : Nat.totient 100492685148739902738465736038 = 33364105229776843555166504000 := by
  rw [← show ((([(2, 1), (3, 1), (251, 1), (511017737, 1), (130579049920791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_3, prime_eightyFiveCE_251, prime_eightyFiveCE_511017737, prime_eightyFiveCE_130579049920791179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736039 : Nat.totient 100492685148739902738465736039 = 86136587270348488061542059456 := by
  rw [← show ((([(7, 1), (14356097878391414676923676577, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_7, prime_eightyFiveCE_14356097878391414676923676577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736040 : Nat.totient 100492685148739902738465736040 = 37832157792829192561621946368 := by
  rw [← show ((([(2, 3), (5, 1), (17, 1), (98909, 1), (1494134613764700867917, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_5, prime_eightyFiveCE_17, prime_eightyFiveCE_98909, prime_eightyFiveCE_1494134613764700867917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736041 : Nat.totient 100492685148739902738465736041 = 66885832844899285930154640000 := by
  rw [← show ((([(3, 1), (613, 1), (6062895001, 1), (9013068554209919, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_3, prime_eightyFiveCE_613, prime_eightyFiveCE_6062895001, prime_eightyFiveCE_9013068554209919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736042 : Nat.totient 100492685148739902738465736042 = 46381239268986342305460307392 := by
  rw [← show ((([(2, 1), (13, 1), (1524090629, 1), (2536006193731104373, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_13, prime_eightyFiveCE_1524090629, prime_eightyFiveCE_2536006193731104373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736043 : Nat.totient 100492685148739902738465736043 = 100492685148734838372621277800 := by
  rw [← show ((([(19921457635901, 1), (5044444386822343, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_19921457635901, prime_eightyFiveCE_5044444386822343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736044 : Nat.totient 100492685148739902738465736044 = 31734522733296713501215699200 := by
  rw [← show ((([(2, 2), (3, 3), (19, 1), (3495397, 1), (93398341, 1), (150010418611, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_3, prime_eightyFiveCE_19, prime_eightyFiveCE_3495397, prime_eightyFiveCE_93398341, prime_eightyFiveCE_150010418611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736045 : Nat.totient 100492685148739902738465736045 = 73085588880690603600976636800 := by
  rw [← show ((([(5, 1), (11, 1), (229545241, 1), (7959824050445415859, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_5, prime_eightyFiveCE_11, prime_eightyFiveCE_229545241, prime_eightyFiveCE_7959824050445415859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736046 : Nat.totient 100492685148739902738465736046 = 43050219130605055827116268288 := by
  rw [← show ((([(2, 1), (7, 3), (2383, 1), (31558433, 1), (1947918857540399, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_7, prime_eightyFiveCE_2383, prime_eightyFiveCE_31558433, prime_eightyFiveCE_1947918857540399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736047 : Nat.totient 100492685148739902738465736047 = 66994142695519245373508223960 := by
  rw [← show ((([(3, 1), (68311, 1), (490368487011559401065059, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_3, prime_eightyFiveCE_68311, prime_eightyFiveCE_490368487011559401065059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736048 : Nat.totient 100492685148739902738465736048 = 49077822979617161802506521920 := by
  rw [← show ((([(2, 4), (43, 1), (146064949344098695840793221, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_43, prime_eightyFiveCE_146064949344098695840793221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736049 : Nat.totient 100492685148739902738465736049 = 99725456651769832891030578880 := by
  rw [← show ((([(131, 1), (916907, 1), (836638540178934816497, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_131, prime_eightyFiveCE_916907, prime_eightyFiveCE_836638540178934816497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736050 : Nat.totient 100492685148739902738465736050 = 26797454070206940791864578560 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (45389, 1), (5475199, 1), (2695831033713737, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_3, prime_eightyFiveCE_5, prime_eightyFiveCE_45389, prime_eightyFiveCE_5475199, prime_eightyFiveCE_2695831033713737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736051 : Nat.totient 100492685148739902738465736051 = 99456677145679401921115587840 := by
  rw [← show ((([(97, 1), (105841973, 1), (9788244058801428071, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_97, prime_eightyFiveCE_105841973, prime_eightyFiveCE_9788244058801428071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736052 : Nat.totient 100492685148739902738465736052 = 49295097394503244773961472000 := by
  rw [← show ((([(2, 2), (53, 1), (15401, 1), (30778657214350177805921, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_53, prime_eightyFiveCE_15401, prime_eightyFiveCE_30778657214350177805921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736053 : Nat.totient 100492685148739902738465736053 = 55571991787321605200994876000 := by
  rw [← show ((([(3, 2), (7, 1), (31, 1), (51455547951223708519439701, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_3, prime_eightyFiveCE_7, prime_eightyFiveCE_31, prime_eightyFiveCE_51455547951223708519439701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736054 : Nat.totient 100492685148739902738465736054 = 48061718399353802362123023592 := by
  rw [← show ((([(2, 1), (23, 1), (82181207, 1), (26583006869076501707, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_23, prime_eightyFiveCE_82181207, prime_eightyFiveCE_26583006869076501707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736055 : Nat.totient 100492685148739902738465736055 = 73795401967629392758932037632 := by
  rw [← show ((([(5, 1), (13, 1), (179, 1), (49173391297, 1), (175645853633069, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_5, prime_eightyFiveCE_13, prime_eightyFiveCE_179, prime_eightyFiveCE_49173391297, prime_eightyFiveCE_175645853633069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736056 : Nat.totient 100492685148739902738465736056 = 29578503376690673991968194560 := by
  rw [← show ((([(2, 3), (3, 1), (11, 1), (47, 1), (139, 1), (4673, 1), (5743, 1), (2171117201865517, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_3, prime_eightyFiveCE_11, prime_eightyFiveCE_47, prime_eightyFiveCE_139, prime_eightyFiveCE_4673, prime_eightyFiveCE_5743, prime_eightyFiveCE_2171117201865517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736057 : Nat.totient 100492685148739902738465736057 = 94581350728225790812673633920 := by
  rw [← show ((([(17, 1), (5911334420514111925792102121, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_17, prime_eightyFiveCE_5911334420514111925792102121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736058 : Nat.totient 100492685148739902738465736058 = 50144693324841142670599912800 := by
  rw [← show ((([(2, 1), (521, 1), (9631, 1), (10013717813891114040779, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_521, prime_eightyFiveCE_9631, prime_eightyFiveCE_10013717813891114040779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736059 : Nat.totient 100492685148739902738465736059 = 66976863701982577165772202528 := by
  rw [← show ((([(3, 1), (3943, 1), (53783, 1), (2851403, 1), (55396559543579, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_3, prime_eightyFiveCE_3943, prime_eightyFiveCE_53783, prime_eightyFiveCE_2851403, prime_eightyFiveCE_55396559543579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736060 : Nat.totient 100492685148739902738465736060 = 34449217708013969800892002560 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (6367, 1), (8240143, 1), (22618171, 1), (604894079, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_5, prime_eightyFiveCE_7, prime_eightyFiveCE_6367, prime_eightyFiveCE_8240143, prime_eightyFiveCE_22618171, prime_eightyFiveCE_604894079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736061 : Nat.totient 100492685148739902738465736061 = 95662810586964940000318619136 := by
  rw [← show ((([(29, 1), (73, 1), (2707, 1), (1477643, 1), (1916839, 1), (6191133647, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_29, prime_eightyFiveCE_73, prime_eightyFiveCE_2707, prime_eightyFiveCE_1477643, prime_eightyFiveCE_1916839, prime_eightyFiveCE_6191133647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736062 : Nat.totient 100492685148739902738465736062 = 32997598108534001937130986960 := by
  rw [← show ((([(2, 1), (3, 2), (67, 1), (7101878672807, 1), (11733130315211, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_3, prime_eightyFiveCE_67, prime_eightyFiveCE_7101878672807, prime_eightyFiveCE_11733130315211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736063 : Nat.totient 100492685148739902738465736063 = 95203515107729228444355507480 := by
  rw [← show ((([(19, 1), (1170311, 1), (4519387318446927568307, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_19, prime_eightyFiveCE_1170311, prime_eightyFiveCE_4519387318446927568307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736064 : Nat.totient 100492685148739902738465736064 = 48885561229364075441840947200 := by
  rw [← show ((([(2, 7), (37, 1), (19861, 1), (157411, 1), (6787136249982769, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_37, prime_eightyFiveCE_19861, prime_eightyFiveCE_157411, prime_eightyFiveCE_6787136249982769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736065 : Nat.totient 100492685148739902738465736065 = 53589790833889168612426358784 := by
  rw [← show ((([(3, 1), (5, 1), (8819, 1), (240829, 1), (6661553, 1), (473521365257, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_3, prime_eightyFiveCE_5, prime_eightyFiveCE_8819, prime_eightyFiveCE_240829, prime_eightyFiveCE_6661553, prime_eightyFiveCE_473521365257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736066 : Nat.totient 100492685148739902738465736066 = 47536516741096485866930749440 := by
  rw [← show ((([(2, 1), (41, 1), (83, 1), (89, 1), (137, 1), (488019913, 1), (2481386350379, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_41, prime_eightyFiveCE_83, prime_eightyFiveCE_89, prime_eightyFiveCE_137, prime_eightyFiveCE_488019913, prime_eightyFiveCE_2481386350379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736067 : Nat.totient 100492685148739902738465736067 = 78305068619895366775352793120 := by
  rw [← show ((([(7, 1), (11, 1), (85133, 1), (15330128236130434066187, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_7, prime_eightyFiveCE_11, prime_eightyFiveCE_85133, prime_eightyFiveCE_15330128236130434066187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736068 : Nat.totient 100492685148739902738465736068 = 30920763618618619508595326592 := by
  rw [← show ((([(2, 2), (3, 1), (13, 1), (579563, 1), (3350383, 1), (331752912387307, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_3, prime_eightyFiveCE_13, prime_eightyFiveCE_579563, prime_eightyFiveCE_3350383, prime_eightyFiveCE_331752912387307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736069 : Nat.totient 100492685148739902738465736069 = 100072209437460424200055269600 := by
  rw [← show ((([(239, 1), (23684041, 1), (17753367593730783731, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_239, prime_eightyFiveCE_23684041, prime_eightyFiveCE_17753367593730783731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736070 : Nat.totient 100492685148739902738465736070 = 40106314736503063707828589056 := by
  rw [← show ((([(2, 1), (5, 1), (839, 1), (937, 1), (12783003238436251768249, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_5, prime_eightyFiveCE_839, prime_eightyFiveCE_937, prime_eightyFiveCE_12783003238436251768249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736071 : Nat.totient 100492685148739902738465736071 = 66994389070355872562631966144 := by
  rw [← show ((([(3, 3), (91229, 1), (40797896521996093160137, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_3, prime_eightyFiveCE_91229, prime_eightyFiveCE_40797896521996093160137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736072 : Nat.totient 100492685148739902738465736072 = 50242584204827235440836648704 := by
  rw [← show ((([(2, 3), (13873, 1), (368107, 1), (2459801155767665219, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_13873, prime_eightyFiveCE_368107, prime_eightyFiveCE_2459801155767665219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736073 : Nat.totient 100492685148739902738465736073 = 100330338322974571716271121988 := by
  rw [← show ((([(619, 1), (162346825765331022194613467, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_619, prime_eightyFiveCE_162346825765331022194613467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736074 : Nat.totient 100492685148739902738465736074 = 27010621279562713330101888000 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (17, 1), (2141, 1), (65738466899247257910101, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_3, prime_eightyFiveCE_7, prime_eightyFiveCE_17, prime_eightyFiveCE_2141, prime_eightyFiveCE_65738466899247257910101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736075 : Nat.totient 100492685148739902738465736075 = 79031535439009008255335764160 := by
  rw [← show ((([(5, 2), (59, 1), (68130633999145696771841177, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_5, prime_eightyFiveCE_59, prime_eightyFiveCE_68130633999145696771841177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736076 : Nat.totient 100492685148739902738465736076 = 50182497158138223349703980992 := by
  rw [← show ((([(2, 2), (787, 1), (31922708115864009764442737, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_787, prime_eightyFiveCE_31922708115864009764442737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736077 : Nat.totient 100492685148739902738465736077 = 63725680633993066688186880000 := by
  rw [← show ((([(3, 1), (23, 1), (181, 1), (40531, 1), (72101, 1), (582859, 1), (4724052017, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_3, prime_eightyFiveCE_23, prime_eightyFiveCE_181, prime_eightyFiveCE_40531, prime_eightyFiveCE_72101, prime_eightyFiveCE_582859, prime_eightyFiveCE_4724052017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736078 : Nat.totient 100492685148739902738465736078 = 45035134180039771340352108000 := by
  rw [← show ((([(2, 1), (11, 1), (71, 1), (4722462781, 1), (13623380208299999, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_11, prime_eightyFiveCE_71, prime_eightyFiveCE_4722462781, prime_eightyFiveCE_13623380208299999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736079 : Nat.totient 100492685148739902738465736079 = 100485182378494618280615205600 := by
  rw [← show ((([(13831, 1), (425027, 1), (170031821, 1), (100538903327, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_13831, prime_eightyFiveCE_425027, prime_eightyFiveCE_170031821, prime_eightyFiveCE_100538903327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736080 : Nat.totient 100492685148739902738465736080 = 26797845139808728541851127808 := by
  rw [← show ((([(2, 4), (3, 2), (5, 1), (131213, 1), (1063714523848203374353, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_3, prime_eightyFiveCE_5, prime_eightyFiveCE_131213, prime_eightyFiveCE_1063714523848203374353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736081 : Nat.totient 100492685148739902738465736081 = 79049520343553674231454063616 := by
  rw [← show ((([(7, 1), (13, 1), (173, 1), (50159, 1), (417542549, 1), (304787637437, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_7, prime_eightyFiveCE_13, prime_eightyFiveCE_173, prime_eightyFiveCE_50159, prime_eightyFiveCE_417542549, prime_eightyFiveCE_304787637437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736082 : Nat.totient 100492685148739902738465736082 = 47601744735911363970869421360 := by
  rw [← show ((([(2, 1), (19, 1), (889879, 1), (2971802173126313942341, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_19, prime_eightyFiveCE_889879, prime_eightyFiveCE_2971802173126313942341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736083 : Nat.totient 100492685148739902738465736083 = 66779704011196268728789200000 := by
  rw [← show ((([(3, 1), (311, 1), (65600401, 1), (1641898525284274151, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_3, prime_eightyFiveCE_311, prime_eightyFiveCE_65600401, prime_eightyFiveCE_1641898525284274151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736084 : Nat.totient 100492685148739902738465736084 = 48623107932420651861164650080 := by
  rw [← show ((([(2, 2), (31, 1), (20399, 1), (41842607, 1), (949478537474587, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_31, prime_eightyFiveCE_20399, prime_eightyFiveCE_41842607, prime_eightyFiveCE_949478537474587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736085 : Nat.totient 100492685148739902738465736085 = 80374248834535733593845030912 := by
  rw [← show ((([(5, 1), (6389, 1), (10987, 1), (11649569927, 1), (24577773697, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_5, prime_eightyFiveCE_6389, prime_eightyFiveCE_10987, prime_eightyFiveCE_11649569927, prime_eightyFiveCE_24577773697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736086 : Nat.totient 100492685148739902738465736086 = 33497561716245257429684579400 := by
  rw [← show ((([(2, 1), (3, 1), (25256326076011, 1), (663151909256971, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_3, prime_eightyFiveCE_25256326076011, prime_eightyFiveCE_663151909256971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736087 : Nat.totient 100492685148739902738465736087 = 100292898343696397049080227968 := by
  rw [← show ((([(503, 1), (648522073, 1), (308064534289350473, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_503, prime_eightyFiveCE_648522073, prime_eightyFiveCE_308064534289350473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736088 : Nat.totient 100492685148739902738465736088 = 43068293635174244030771029728 := by
  rw [← show ((([(2, 3), (7, 1), (1794512234798926834615459573, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_7, prime_eightyFiveCE_1794512234798926834615459573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736089 : Nat.totient 100492685148739902738465736089 = 60238661778346482299039402880 := by
  rw [← show ((([(3, 2), (11, 1), (109, 1), (563, 1), (1175659, 1), (14069640166508687, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_3, prime_eightyFiveCE_11, prime_eightyFiveCE_109, prime_eightyFiveCE_563, prime_eightyFiveCE_1175659, prime_eightyFiveCE_14069640166508687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736090 : Nat.totient 100492685148739902738465736090 = 38808331980010602924570406464 := by
  rw [← show ((([(2, 1), (5, 1), (29, 1), (14723, 1), (23536405658690227286527, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_5, prime_eightyFiveCE_29, prime_eightyFiveCE_14723, prime_eightyFiveCE_23536405658690227286527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736091 : Nat.totient 100492685148739902738465736091 = 90810230691918938243097600000 := by
  rw [← show ((([(17, 1), (43, 1), (61, 1), (1613, 1), (162751, 1), (441011, 1), (19466137357, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_17, prime_eightyFiveCE_43, prime_eightyFiveCE_61, prime_eightyFiveCE_1613, prime_eightyFiveCE_162751, prime_eightyFiveCE_441011, prime_eightyFiveCE_19466137357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736092 : Nat.totient 100492685148739902738465736092 = 33068373582777335343559997440 := by
  rw [← show ((([(2, 2), (3, 1), (113, 1), (263, 1), (5081, 1), (55458716933738039219, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_3, prime_eightyFiveCE_113, prime_eightyFiveCE_263, prime_eightyFiveCE_5081, prime_eightyFiveCE_55458716933738039219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736093 : Nat.totient 100492685148739902738465736093 = 100475513105924015147209734816 := by
  rw [← show ((([(5867, 1), (2305487, 1), (7429433243596965817, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_5867, prime_eightyFiveCE_2305487, prime_eightyFiveCE_7429433243596965817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736094 : Nat.totient 100492685148739902738465736094 = 46311085931208977263021603200 := by
  rw [← show ((([(2, 1), (13, 1), (1181, 1), (1531, 1), (75743, 1), (28222371991449403, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_13, prime_eightyFiveCE_1181, prime_eightyFiveCE_1531, prime_eightyFiveCE_75743, prime_eightyFiveCE_28222371991449403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736095 : Nat.totient 100492685148739902738465736095 = 45937118407473970299988335936 := by
  rw [← show ((([(3, 1), (5, 1), (7, 2), (19183, 1), (7127391007609125479119, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_3, prime_eightyFiveCE_5, prime_eightyFiveCE_7, prime_eightyFiveCE_19183, prime_eightyFiveCE_7127391007609125479119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736096 : Nat.totient 100492685148739902738465736096 = 50024223606878878745349212160 := by
  rw [← show ((([(2, 5), (227, 1), (117427, 1), (145661, 1), (808811583097337, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_227, prime_eightyFiveCE_117427, prime_eightyFiveCE_145661, prime_eightyFiveCE_808811583097337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736097 : Nat.totient 100492685148739902738465736097 = 100483722532427564936640233728 := by
  rw [← show ((([(11213, 1), (219567473, 1), (40817333031825653, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_11213, prime_eightyFiveCE_219567473, prime_eightyFiveCE_40817333031825653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736098 : Nat.totient 100492685148739902738465736098 = 33497561715713353156801144536 := by
  rw [← show ((([(2, 1), (3, 4), (62814480863, 1), (9875512914298783, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_3, prime_eightyFiveCE_62814480863, prime_eightyFiveCE_9875512914298783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736099 : Nat.totient 100492685148739902738465736099 = 100492685148739902738465736098 := by
  rw [← show ((([(100492685148739902738465736099, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_100492685148739902738465736099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736100 : Nat.totient 100492685148739902738465736100 = 34925582660389243207932624000 := by
  rw [← show ((([(2, 2), (5, 2), (11, 1), (23, 1), (1231, 1), (3226679846673063858827, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_5, prime_eightyFiveCE_11, prime_eightyFiveCE_23, prime_eightyFiveCE_1231, prime_eightyFiveCE_3226679846673063858827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736101 : Nat.totient 100492685148739902738465736101 = 61751987689918928199994538496 := by
  rw [← show ((([(3, 1), (19, 1), (37, 1), (36457, 1), (23561143, 1), (55472863864039, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_3, prime_eightyFiveCE_19, prime_eightyFiveCE_37, prime_eightyFiveCE_36457, prime_eightyFiveCE_23561143, prime_eightyFiveCE_55472863864039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736102 : Nat.totient 100492685148739902738465736102 = 43056713020271380608761051040 := by
  rw [← show ((([(2, 1), (7, 1), (3719, 1), (12142339087, 1), (158956349261581, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736102 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_2, prime_eightyFiveCE_7, prime_eightyFiveCE_3719, prime_eightyFiveCE_12142339087, prime_eightyFiveCE_158956349261581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFiveCE_100492685148739902738465736103 : Nat.totient 100492685148739902738465736103 = 97109548654165212963626005632 := by
  rw [← show ((([(47, 1), (79, 1), (2242848599, 1), (12067284266216369, 1)] : List FactorBlock).map factorBlockValue).prod) = 100492685148739902738465736103 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFiveCE_47, prime_eightyFiveCE_79, prime_eightyFiveCE_2242848599, prime_eightyFiveCE_12067284266216369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64EightyFiveCE : certifiedKill 3 100492685148739902738465735999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_eightyFiveCE_100492685148739902738465736000, phi_eightyFiveCE_100492685148739902738465736001, phi_eightyFiveCE_100492685148739902738465736002,
    phi_eightyFiveCE_100492685148739902738465736003, phi_eightyFiveCE_100492685148739902738465736004, phi_eightyFiveCE_100492685148739902738465736005,
    phi_eightyFiveCE_100492685148739902738465736006, phi_eightyFiveCE_100492685148739902738465736007, phi_eightyFiveCE_100492685148739902738465736008,
    phi_eightyFiveCE_100492685148739902738465736009, phi_eightyFiveCE_100492685148739902738465736010, phi_eightyFiveCE_100492685148739902738465736011,
    phi_eightyFiveCE_100492685148739902738465736012, phi_eightyFiveCE_100492685148739902738465736013, phi_eightyFiveCE_100492685148739902738465736014,
    phi_eightyFiveCE_100492685148739902738465736015, phi_eightyFiveCE_100492685148739902738465736016, phi_eightyFiveCE_100492685148739902738465736017,
    phi_eightyFiveCE_100492685148739902738465736018, phi_eightyFiveCE_100492685148739902738465736019, phi_eightyFiveCE_100492685148739902738465736020,
    phi_eightyFiveCE_100492685148739902738465736021, phi_eightyFiveCE_100492685148739902738465736022, phi_eightyFiveCE_100492685148739902738465736023,
    phi_eightyFiveCE_100492685148739902738465736024, phi_eightyFiveCE_100492685148739902738465736025, phi_eightyFiveCE_100492685148739902738465736026,
    phi_eightyFiveCE_100492685148739902738465736027, phi_eightyFiveCE_100492685148739902738465736028, phi_eightyFiveCE_100492685148739902738465736029,
    phi_eightyFiveCE_100492685148739902738465736030, phi_eightyFiveCE_100492685148739902738465736031, phi_eightyFiveCE_100492685148739902738465736032,
    phi_eightyFiveCE_100492685148739902738465736033, phi_eightyFiveCE_100492685148739902738465736034, phi_eightyFiveCE_100492685148739902738465736035,
    phi_eightyFiveCE_100492685148739902738465736036, phi_eightyFiveCE_100492685148739902738465736037, phi_eightyFiveCE_100492685148739902738465736038,
    phi_eightyFiveCE_100492685148739902738465736039, phi_eightyFiveCE_100492685148739902738465736040, phi_eightyFiveCE_100492685148739902738465736041,
    phi_eightyFiveCE_100492685148739902738465736042, phi_eightyFiveCE_100492685148739902738465736043, phi_eightyFiveCE_100492685148739902738465736044,
    phi_eightyFiveCE_100492685148739902738465736045, phi_eightyFiveCE_100492685148739902738465736046, phi_eightyFiveCE_100492685148739902738465736047,
    phi_eightyFiveCE_100492685148739902738465736048, phi_eightyFiveCE_100492685148739902738465736049, phi_eightyFiveCE_100492685148739902738465736050,
    phi_eightyFiveCE_100492685148739902738465736051, phi_eightyFiveCE_100492685148739902738465736052, phi_eightyFiveCE_100492685148739902738465736053,
    phi_eightyFiveCE_100492685148739902738465736054, phi_eightyFiveCE_100492685148739902738465736055, phi_eightyFiveCE_100492685148739902738465736056,
    phi_eightyFiveCE_100492685148739902738465736057, phi_eightyFiveCE_100492685148739902738465736058, phi_eightyFiveCE_100492685148739902738465736059,
    phi_eightyFiveCE_100492685148739902738465736060, phi_eightyFiveCE_100492685148739902738465736061, phi_eightyFiveCE_100492685148739902738465736062,
    phi_eightyFiveCE_100492685148739902738465736063, phi_eightyFiveCE_100492685148739902738465736064, phi_eightyFiveCE_100492685148739902738465736065,
    phi_eightyFiveCE_100492685148739902738465736066, phi_eightyFiveCE_100492685148739902738465736067, phi_eightyFiveCE_100492685148739902738465736068,
    phi_eightyFiveCE_100492685148739902738465736069, phi_eightyFiveCE_100492685148739902738465736070, phi_eightyFiveCE_100492685148739902738465736071,
    phi_eightyFiveCE_100492685148739902738465736072, phi_eightyFiveCE_100492685148739902738465736073, phi_eightyFiveCE_100492685148739902738465736074,
    phi_eightyFiveCE_100492685148739902738465736075, phi_eightyFiveCE_100492685148739902738465736076, phi_eightyFiveCE_100492685148739902738465736077,
    phi_eightyFiveCE_100492685148739902738465736078, phi_eightyFiveCE_100492685148739902738465736079, phi_eightyFiveCE_100492685148739902738465736080,
    phi_eightyFiveCE_100492685148739902738465736081, phi_eightyFiveCE_100492685148739902738465736082, phi_eightyFiveCE_100492685148739902738465736083,
    phi_eightyFiveCE_100492685148739902738465736084, phi_eightyFiveCE_100492685148739902738465736085, phi_eightyFiveCE_100492685148739902738465736086,
    phi_eightyFiveCE_100492685148739902738465736087, phi_eightyFiveCE_100492685148739902738465736088, phi_eightyFiveCE_100492685148739902738465736089,
    phi_eightyFiveCE_100492685148739902738465736090, phi_eightyFiveCE_100492685148739902738465736091, phi_eightyFiveCE_100492685148739902738465736092,
    phi_eightyFiveCE_100492685148739902738465736093, phi_eightyFiveCE_100492685148739902738465736094, phi_eightyFiveCE_100492685148739902738465736095,
    phi_eightyFiveCE_100492685148739902738465736096, phi_eightyFiveCE_100492685148739902738465736097, phi_eightyFiveCE_100492685148739902738465736098,
    phi_eightyFiveCE_100492685148739902738465736099, phi_eightyFiveCE_100492685148739902738465736100, phi_eightyFiveCE_100492685148739902738465736101,
    phi_eightyFiveCE_100492685148739902738465736102, phi_eightyFiveCE_100492685148739902738465736103
    ]

end TotientTailPeriodKiller
end Erdos249257
