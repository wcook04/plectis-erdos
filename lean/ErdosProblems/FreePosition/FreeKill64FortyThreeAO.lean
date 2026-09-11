import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 43P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fortyThreeAOFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fortyThreeAOFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fortyThreeAOFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fortyThreeAOFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fortyThreeAOFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fortyThreeAOFastPow a n * fortyThreeAOFastPow a n * a
        else fortyThreeAOFastPow a n * fortyThreeAOFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fortyThreeAO_2 : Nat.Prime 2 := by norm_num
private theorem prime_fortyThreeAO_3 : Nat.Prime 3 := by norm_num
private theorem prime_fortyThreeAO_5 : Nat.Prime 5 := by norm_num
private theorem prime_fortyThreeAO_7 : Nat.Prime 7 := by norm_num
private theorem prime_fortyThreeAO_11 : Nat.Prime 11 := by norm_num
private theorem prime_fortyThreeAO_13 : Nat.Prime 13 := by norm_num
private theorem prime_fortyThreeAO_17 : Nat.Prime 17 := by norm_num
private theorem prime_fortyThreeAO_19 : Nat.Prime 19 := by norm_num
private theorem prime_fortyThreeAO_23 : Nat.Prime 23 := by norm_num
private theorem prime_fortyThreeAO_29 : Nat.Prime 29 := by norm_num
private theorem prime_fortyThreeAO_31 : Nat.Prime 31 := by norm_num
private theorem prime_fortyThreeAO_37 : Nat.Prime 37 := by norm_num
private theorem prime_fortyThreeAO_41 : Nat.Prime 41 := by norm_num
private theorem prime_fortyThreeAO_43 : Nat.Prime 43 := by norm_num
private theorem prime_fortyThreeAO_47 : Nat.Prime 47 := by norm_num
private theorem prime_fortyThreeAO_53 : Nat.Prime 53 := by norm_num
private theorem prime_fortyThreeAO_59 : Nat.Prime 59 := by norm_num
private theorem prime_fortyThreeAO_61 : Nat.Prime 61 := by norm_num
private theorem prime_fortyThreeAO_67 : Nat.Prime 67 := by norm_num
private theorem prime_fortyThreeAO_71 : Nat.Prime 71 := by norm_num
private theorem prime_fortyThreeAO_73 : Nat.Prime 73 := by norm_num
private theorem prime_fortyThreeAO_79 : Nat.Prime 79 := by norm_num
private theorem prime_fortyThreeAO_83 : Nat.Prime 83 := by norm_num
private theorem prime_fortyThreeAO_89 : Nat.Prime 89 := by norm_num
private theorem prime_fortyThreeAO_97 : Nat.Prime 97 := by norm_num
private theorem prime_fortyThreeAO_101 : Nat.Prime 101 := by norm_num
private theorem prime_fortyThreeAO_103 : Nat.Prime 103 := by norm_num
private theorem prime_fortyThreeAO_107 : Nat.Prime 107 := by norm_num
private theorem prime_fortyThreeAO_109 : Nat.Prime 109 := by norm_num
private theorem prime_fortyThreeAO_113 : Nat.Prime 113 := by norm_num
private theorem prime_fortyThreeAO_127 : Nat.Prime 127 := by norm_num
private theorem prime_fortyThreeAO_131 : Nat.Prime 131 := by norm_num
private theorem prime_fortyThreeAO_137 : Nat.Prime 137 := by norm_num
private theorem prime_fortyThreeAO_149 : Nat.Prime 149 := by norm_num
private theorem prime_fortyThreeAO_151 : Nat.Prime 151 := by norm_num
private theorem prime_fortyThreeAO_157 : Nat.Prime 157 := by norm_num
private theorem prime_fortyThreeAO_163 : Nat.Prime 163 := by norm_num
private theorem prime_fortyThreeAO_167 : Nat.Prime 167 := by norm_num
private theorem prime_fortyThreeAO_173 : Nat.Prime 173 := by norm_num
private theorem prime_fortyThreeAO_179 : Nat.Prime 179 := by norm_num
private theorem prime_fortyThreeAO_181 : Nat.Prime 181 := by norm_num
private theorem prime_fortyThreeAO_191 : Nat.Prime 191 := by norm_num
private theorem prime_fortyThreeAO_193 : Nat.Prime 193 := by norm_num
private theorem prime_fortyThreeAO_197 : Nat.Prime 197 := by norm_num
private theorem prime_fortyThreeAO_199 : Nat.Prime 199 := by norm_num
private theorem prime_fortyThreeAO_211 : Nat.Prime 211 := by norm_num
private theorem prime_fortyThreeAO_223 : Nat.Prime 223 := by norm_num
private theorem prime_fortyThreeAO_227 : Nat.Prime 227 := by norm_num
private theorem prime_fortyThreeAO_229 : Nat.Prime 229 := by norm_num
private theorem prime_fortyThreeAO_233 : Nat.Prime 233 := by norm_num
private theorem prime_fortyThreeAO_239 : Nat.Prime 239 := by norm_num
private theorem prime_fortyThreeAO_241 : Nat.Prime 241 := by norm_num
private theorem prime_fortyThreeAO_251 : Nat.Prime 251 := by norm_num
private theorem prime_fortyThreeAO_257 : Nat.Prime 257 := by norm_num
private theorem prime_fortyThreeAO_269 : Nat.Prime 269 := by norm_num
private theorem prime_fortyThreeAO_277 : Nat.Prime 277 := by norm_num
private theorem prime_fortyThreeAO_283 : Nat.Prime 283 := by norm_num
private theorem prime_fortyThreeAO_307 : Nat.Prime 307 := by norm_num
private theorem prime_fortyThreeAO_317 : Nat.Prime 317 := by norm_num
private theorem prime_fortyThreeAO_331 : Nat.Prime 331 := by norm_num
private theorem prime_fortyThreeAO_347 : Nat.Prime 347 := by norm_num
private theorem prime_fortyThreeAO_349 : Nat.Prime 349 := by norm_num
private theorem prime_fortyThreeAO_359 : Nat.Prime 359 := by norm_num
private theorem prime_fortyThreeAO_367 : Nat.Prime 367 := by norm_num
private theorem prime_fortyThreeAO_373 : Nat.Prime 373 := by norm_num
private theorem prime_fortyThreeAO_379 : Nat.Prime 379 := by norm_num
private theorem prime_fortyThreeAO_397 : Nat.Prime 397 := by norm_num
private theorem prime_fortyThreeAO_439 : Nat.Prime 439 := by norm_num
private theorem prime_fortyThreeAO_449 : Nat.Prime 449 := by norm_num
private theorem prime_fortyThreeAO_457 : Nat.Prime 457 := by norm_num
private theorem prime_fortyThreeAO_479 : Nat.Prime 479 := by norm_num
private theorem prime_fortyThreeAO_487 : Nat.Prime 487 := by norm_num
private theorem prime_fortyThreeAO_491 : Nat.Prime 491 := by norm_num
private theorem prime_fortyThreeAO_499 : Nat.Prime 499 := by norm_num
private theorem prime_fortyThreeAO_503 : Nat.Prime 503 := by norm_num
private theorem prime_fortyThreeAO_521 : Nat.Prime 521 := by norm_num
private theorem prime_fortyThreeAO_557 : Nat.Prime 557 := by norm_num
private theorem prime_fortyThreeAO_563 : Nat.Prime 563 := by norm_num
private theorem prime_fortyThreeAO_571 : Nat.Prime 571 := by norm_num
private theorem prime_fortyThreeAO_587 : Nat.Prime 587 := by norm_num
private theorem prime_fortyThreeAO_593 : Nat.Prime 593 := by norm_num
private theorem prime_fortyThreeAO_599 : Nat.Prime 599 := by norm_num
private theorem prime_fortyThreeAO_607 : Nat.Prime 607 := by norm_num
private theorem prime_fortyThreeAO_641 : Nat.Prime 641 := by norm_num
private theorem prime_fortyThreeAO_661 : Nat.Prime 661 := by norm_num
private theorem prime_fortyThreeAO_691 : Nat.Prime 691 := by norm_num
private theorem prime_fortyThreeAO_709 : Nat.Prime 709 := by norm_num
private theorem prime_fortyThreeAO_719 : Nat.Prime 719 := by norm_num
private theorem prime_fortyThreeAO_727 : Nat.Prime 727 := by norm_num
private theorem prime_fortyThreeAO_733 : Nat.Prime 733 := by norm_num
private theorem prime_fortyThreeAO_769 : Nat.Prime 769 := by norm_num
private theorem prime_fortyThreeAO_787 : Nat.Prime 787 := by norm_num
private theorem prime_fortyThreeAO_811 : Nat.Prime 811 := by norm_num
private theorem prime_fortyThreeAO_821 : Nat.Prime 821 := by norm_num
private theorem prime_fortyThreeAO_829 : Nat.Prime 829 := by norm_num
private theorem prime_fortyThreeAO_863 : Nat.Prime 863 := by norm_num
private theorem prime_fortyThreeAO_877 : Nat.Prime 877 := by norm_num
private theorem prime_fortyThreeAO_907 : Nat.Prime 907 := by norm_num
private theorem prime_fortyThreeAO_937 : Nat.Prime 937 := by norm_num
private theorem prime_fortyThreeAO_947 : Nat.Prime 947 := by norm_num
private theorem prime_fortyThreeAO_953 : Nat.Prime 953 := by norm_num
private theorem prime_fortyThreeAO_971 : Nat.Prime 971 := by norm_num
private theorem prime_fortyThreeAO_991 : Nat.Prime 991 := by norm_num
private theorem prime_fortyThreeAO_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_fortyThreeAO_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_fortyThreeAO_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_fortyThreeAO_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_fortyThreeAO_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_fortyThreeAO_1171 : Nat.Prime 1171 := by norm_num
private theorem prime_fortyThreeAO_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_fortyThreeAO_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_fortyThreeAO_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_fortyThreeAO_1451 : Nat.Prime 1451 := by norm_num
private theorem prime_fortyThreeAO_1499 : Nat.Prime 1499 := by norm_num
private theorem prime_fortyThreeAO_1621 : Nat.Prime 1621 := by norm_num
private theorem prime_fortyThreeAO_1637 : Nat.Prime 1637 := by norm_num
private theorem prime_fortyThreeAO_1657 : Nat.Prime 1657 := by norm_num
private theorem prime_fortyThreeAO_1693 : Nat.Prime 1693 := by norm_num
private theorem prime_fortyThreeAO_1777 : Nat.Prime 1777 := by norm_num
private theorem prime_fortyThreeAO_1823 : Nat.Prime 1823 := by norm_num
private theorem prime_fortyThreeAO_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_fortyThreeAO_1931 : Nat.Prime 1931 := by norm_num
private theorem prime_fortyThreeAO_2063 : Nat.Prime 2063 := by norm_num
private theorem prime_fortyThreeAO_2083 : Nat.Prime 2083 := by norm_num
private theorem prime_fortyThreeAO_2131 : Nat.Prime 2131 := by norm_num
private theorem prime_fortyThreeAO_2267 : Nat.Prime 2267 := by norm_num
private theorem prime_fortyThreeAO_2273 : Nat.Prime 2273 := by norm_num
private theorem prime_fortyThreeAO_2297 : Nat.Prime 2297 := by norm_num
private theorem prime_fortyThreeAO_2351 : Nat.Prime 2351 := by norm_num
private theorem prime_fortyThreeAO_2399 : Nat.Prime 2399 := by norm_num
private theorem prime_fortyThreeAO_2423 : Nat.Prime 2423 := by norm_num
private theorem prime_fortyThreeAO_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_fortyThreeAO_2539 : Nat.Prime 2539 := by norm_num
private theorem prime_fortyThreeAO_2633 : Nat.Prime 2633 := by norm_num
private theorem prime_fortyThreeAO_2663 : Nat.Prime 2663 := by norm_num
private theorem prime_fortyThreeAO_2749 : Nat.Prime 2749 := by norm_num
private theorem prime_fortyThreeAO_2879 : Nat.Prime 2879 := by norm_num
private theorem prime_fortyThreeAO_3061 : Nat.Prime 3061 := by norm_num
private theorem prime_fortyThreeAO_3089 : Nat.Prime 3089 := by norm_num
private theorem prime_fortyThreeAO_3253 : Nat.Prime 3253 := by norm_num
private theorem prime_fortyThreeAO_3343 : Nat.Prime 3343 := by norm_num
private theorem prime_fortyThreeAO_3373 : Nat.Prime 3373 := by norm_num
private theorem prime_fortyThreeAO_3499 : Nat.Prime 3499 := by norm_num
private theorem prime_fortyThreeAO_3539 : Nat.Prime 3539 := by norm_num
private theorem prime_fortyThreeAO_3607 : Nat.Prime 3607 := by norm_num
private theorem prime_fortyThreeAO_3779 : Nat.Prime 3779 := by norm_num
private theorem prime_fortyThreeAO_3881 : Nat.Prime 3881 := by norm_num
private theorem prime_fortyThreeAO_3889 : Nat.Prime 3889 := by norm_num
private theorem prime_fortyThreeAO_3917 : Nat.Prime 3917 := by norm_num
private theorem prime_fortyThreeAO_4027 : Nat.Prime 4027 := by norm_num
private theorem prime_fortyThreeAO_4057 : Nat.Prime 4057 := by norm_num
private theorem prime_fortyThreeAO_4507 : Nat.Prime 4507 := by norm_num
private theorem prime_fortyThreeAO_4933 : Nat.Prime 4933 := by norm_num
private theorem prime_fortyThreeAO_5003 : Nat.Prime 5003 := by norm_num
private theorem prime_fortyThreeAO_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fortyThreeAO_5011 : Nat.Prime 5011 := by norm_num
private theorem prime_fortyThreeAO_5021 : Nat.Prime 5021 := by norm_num
private theorem prime_fortyThreeAO_5227 : Nat.Prime 5227 := by norm_num
private theorem prime_fortyThreeAO_5273 : Nat.Prime 5273 := by norm_num
private theorem prime_fortyThreeAO_5413 : Nat.Prime 5413 := by norm_num
private theorem prime_fortyThreeAO_5437 : Nat.Prime 5437 := by norm_num
private theorem prime_fortyThreeAO_5477 : Nat.Prime 5477 := by norm_num
private theorem prime_fortyThreeAO_5507 : Nat.Prime 5507 := by norm_num
private theorem prime_fortyThreeAO_5569 : Nat.Prime 5569 := by norm_num
private theorem prime_fortyThreeAO_5573 : Nat.Prime 5573 := by norm_num
private theorem prime_fortyThreeAO_5647 : Nat.Prime 5647 := by norm_num
private theorem prime_fortyThreeAO_5711 : Nat.Prime 5711 := by norm_num
private theorem prime_fortyThreeAO_5801 : Nat.Prime 5801 := by norm_num
private theorem prime_fortyThreeAO_5881 : Nat.Prime 5881 := by norm_num
private theorem prime_fortyThreeAO_6007 : Nat.Prime 6007 := by norm_num
private theorem prime_fortyThreeAO_6091 : Nat.Prime 6091 := by norm_num
private theorem prime_fortyThreeAO_6271 : Nat.Prime 6271 := by norm_num
private theorem prime_fortyThreeAO_6473 : Nat.Prime 6473 := by norm_num
private theorem prime_fortyThreeAO_6577 : Nat.Prime 6577 := by norm_num
private theorem prime_fortyThreeAO_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_fortyThreeAO_6779 : Nat.Prime 6779 := by norm_num
private theorem prime_fortyThreeAO_7013 : Nat.Prime 7013 := by norm_num
private theorem prime_fortyThreeAO_7237 : Nat.Prime 7237 := by norm_num
private theorem prime_fortyThreeAO_7603 : Nat.Prime 7603 := by norm_num
private theorem prime_fortyThreeAO_8123 : Nat.Prime 8123 := by norm_num
private theorem prime_fortyThreeAO_8543 : Nat.Prime 8543 := by norm_num
private theorem prime_fortyThreeAO_8623 : Nat.Prime 8623 := by norm_num
private theorem prime_fortyThreeAO_9059 : Nat.Prime 9059 := by norm_num
private theorem prime_fortyThreeAO_9391 : Nat.Prime 9391 := by norm_num
private theorem prime_fortyThreeAO_9479 : Nat.Prime 9479 := by norm_num
private theorem prime_fortyThreeAO_9601 : Nat.Prime 9601 := by norm_num
private theorem prime_fortyThreeAO_10531 : Nat.Prime 10531 := by norm_num
private theorem prime_fortyThreeAO_10711 : Nat.Prime 10711 := by norm_num
private theorem prime_fortyThreeAO_11113 : Nat.Prime 11113 := by norm_num
private theorem prime_fortyThreeAO_11383 : Nat.Prime 11383 := by norm_num
private theorem prime_fortyThreeAO_11813 : Nat.Prime 11813 := by norm_num
private theorem prime_fortyThreeAO_12541 : Nat.Prime 12541 := by norm_num
private theorem prime_fortyThreeAO_12589 : Nat.Prime 12589 := by norm_num
private theorem prime_fortyThreeAO_12841 : Nat.Prime 12841 := by norm_num
private theorem prime_fortyThreeAO_13613 : Nat.Prime 13613 := by norm_num
private theorem prime_fortyThreeAO_13799 : Nat.Prime 13799 := by norm_num
private theorem prime_fortyThreeAO_15131 : Nat.Prime 15131 := by norm_num
private theorem prime_fortyThreeAO_15731 : Nat.Prime 15731 := by norm_num
private theorem prime_fortyThreeAO_15803 : Nat.Prime 15803 := by norm_num
private theorem prime_fortyThreeAO_16823 : Nat.Prime 16823 := by norm_num
private theorem prime_fortyThreeAO_17099 : Nat.Prime 17099 := by norm_num
private theorem prime_fortyThreeAO_17401 : Nat.Prime 17401 := by norm_num
private theorem prime_fortyThreeAO_17627 : Nat.Prime 17627 := by norm_num
private theorem prime_fortyThreeAO_17971 : Nat.Prime 17971 := by norm_num
private theorem prime_fortyThreeAO_22031 : Nat.Prime 22031 := by norm_num
private theorem prime_fortyThreeAO_22433 : Nat.Prime 22433 := by norm_num
private theorem prime_fortyThreeAO_23017 : Nat.Prime 23017 := by norm_num
private theorem prime_fortyThreeAO_23981 : Nat.Prime 23981 := by norm_num
private theorem prime_fortyThreeAO_25357 : Nat.Prime 25357 := by norm_num
private theorem prime_fortyThreeAO_25717 : Nat.Prime 25717 := by norm_num
private theorem prime_fortyThreeAO_26029 : Nat.Prime 26029 := by norm_num
private theorem prime_fortyThreeAO_26171 : Nat.Prime 26171 := by norm_num
private theorem prime_fortyThreeAO_27427 : Nat.Prime 27427 := by norm_num
private theorem prime_fortyThreeAO_28001 : Nat.Prime 28001 := by norm_num
private theorem prime_fortyThreeAO_29167 : Nat.Prime 29167 := by norm_num
private theorem prime_fortyThreeAO_31991 : Nat.Prime 31991 := by norm_num
private theorem prime_fortyThreeAO_32497 : Nat.Prime 32497 := by norm_num
private theorem prime_fortyThreeAO_33617 : Nat.Prime 33617 := by norm_num
private theorem prime_fortyThreeAO_33791 : Nat.Prime 33791 := by norm_num
private theorem prime_fortyThreeAO_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_fortyThreeAO_35531 : Nat.Prime 35531 := by norm_num
private theorem prime_fortyThreeAO_36013 : Nat.Prime 36013 := by norm_num
private theorem prime_fortyThreeAO_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_fortyThreeAO_37589 : Nat.Prime 37589 := by norm_num
private theorem prime_fortyThreeAO_37747 : Nat.Prime 37747 := by norm_num
private theorem prime_fortyThreeAO_39119 : Nat.Prime 39119 := by norm_num
private theorem prime_fortyThreeAO_41999 : Nat.Prime 41999 := by norm_num
private theorem prime_fortyThreeAO_42979 : Nat.Prime 42979 := by norm_num
private theorem prime_fortyThreeAO_43543 : Nat.Prime 43543 := by norm_num
private theorem prime_fortyThreeAO_45053 : Nat.Prime 45053 := by norm_num
private theorem prime_fortyThreeAO_47293 : Nat.Prime 47293 := by norm_num
private theorem prime_fortyThreeAO_47653 : Nat.Prime 47653 := by norm_num
private theorem prime_fortyThreeAO_47743 : Nat.Prime 47743 := by norm_num
private theorem prime_fortyThreeAO_50321 : Nat.Prime 50321 := by norm_num
private theorem prime_fortyThreeAO_54163 : Nat.Prime 54163 := by norm_num
private theorem prime_fortyThreeAO_54949 : Nat.Prime 54949 := by norm_num
private theorem prime_fortyThreeAO_57329 : Nat.Prime 57329 := by norm_num
private theorem prime_fortyThreeAO_57667 : Nat.Prime 57667 := by norm_num
private theorem prime_fortyThreeAO_58601 : Nat.Prime 58601 := by norm_num
private theorem prime_fortyThreeAO_60539 : Nat.Prime 60539 := by norm_num
private theorem prime_fortyThreeAO_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_fortyThreeAO_62383 : Nat.Prime 62383 := by norm_num
private theorem prime_fortyThreeAO_67819 : Nat.Prime 67819 := by norm_num
private theorem prime_fortyThreeAO_70381 : Nat.Prime 70381 := by norm_num
private theorem prime_fortyThreeAO_71147 : Nat.Prime 71147 := by norm_num
private theorem prime_fortyThreeAO_72823 : Nat.Prime 72823 := by norm_num
private theorem prime_fortyThreeAO_72889 : Nat.Prime 72889 := by norm_num
private theorem prime_fortyThreeAO_73009 : Nat.Prime 73009 := by norm_num
private theorem prime_fortyThreeAO_73459 : Nat.Prime 73459 := by norm_num
private theorem prime_fortyThreeAO_74201 : Nat.Prime 74201 := by norm_num
private theorem prime_fortyThreeAO_76801 : Nat.Prime 76801 := by norm_num
private theorem prime_fortyThreeAO_77839 : Nat.Prime 77839 := by norm_num
private theorem prime_fortyThreeAO_78791 : Nat.Prime 78791 := by norm_num
private theorem prime_fortyThreeAO_81527 : Nat.Prime 81527 := by norm_num
private theorem prime_fortyThreeAO_93253 : Nat.Prime 93253 := by norm_num
private theorem prime_fortyThreeAO_99487 : Nat.Prime 99487 := by norm_num
private theorem prime_fortyThreeAO_100057 : Nat.Prime 100057 := by norm_num
private theorem prime_fortyThreeAO_101957 : Nat.Prime 101957 := by norm_num
private theorem prime_fortyThreeAO_102181 : Nat.Prime 102181 := by norm_num
private theorem prime_fortyThreeAO_102587 : Nat.Prime 102587 := by norm_num
private theorem prime_fortyThreeAO_111031 : Nat.Prime 111031 := by norm_num
private theorem prime_fortyThreeAO_115657 : Nat.Prime 115657 := by norm_num
private theorem prime_fortyThreeAO_123407 : Nat.Prime 123407 := by norm_num
private theorem prime_fortyThreeAO_130211 : Nat.Prime 130211 := by norm_num
private theorem prime_fortyThreeAO_133949 : Nat.Prime 133949 := by norm_num
private theorem prime_fortyThreeAO_134581 : Nat.Prime 134581 := by norm_num
private theorem prime_fortyThreeAO_141397 : Nat.Prime 141397 := by norm_num
private theorem prime_fortyThreeAO_142733 : Nat.Prime 142733 := by norm_num
private theorem prime_fortyThreeAO_152063 : Nat.Prime 152063 := by norm_num
private theorem prime_fortyThreeAO_162527 : Nat.Prime 162527 := by norm_num
private theorem prime_fortyThreeAO_177943 : Nat.Prime 177943 := by norm_num
private theorem prime_fortyThreeAO_179533 : Nat.Prime 179533 := by norm_num
private theorem prime_fortyThreeAO_181183 : Nat.Prime 181183 := by norm_num
private theorem prime_fortyThreeAO_187897 : Nat.Prime 187897 := by norm_num
private theorem prime_fortyThreeAO_189407 : Nat.Prime 189407 := by norm_num
private theorem prime_fortyThreeAO_191579 : Nat.Prime 191579 := by norm_num
private theorem prime_fortyThreeAO_195389 : Nat.Prime 195389 := by norm_num
private theorem prime_fortyThreeAO_201049 : Nat.Prime 201049 := by norm_num
private theorem prime_fortyThreeAO_202757 : Nat.Prime 202757 := by norm_num
private theorem prime_fortyThreeAO_218623 : Nat.Prime 218623 := by norm_num
private theorem prime_fortyThreeAO_223339 : Nat.Prime 223339 := by norm_num
private theorem prime_fortyThreeAO_232049 : Nat.Prime 232049 := by norm_num
private theorem prime_fortyThreeAO_234287 : Nat.Prime 234287 := by norm_num
private theorem prime_fortyThreeAO_254491 : Nat.Prime 254491 := by norm_num
private theorem prime_fortyThreeAO_264787 : Nat.Prime 264787 := by norm_num
private theorem prime_fortyThreeAO_266953 : Nat.Prime 266953 := by norm_num
private theorem prime_fortyThreeAO_270229 : Nat.Prime 270229 := by norm_num
private theorem prime_fortyThreeAO_284227 : Nat.Prime 284227 := by norm_num
private theorem prime_fortyThreeAO_287059 : Nat.Prime 287059 := by norm_num
private theorem prime_fortyThreeAO_303053 : Nat.Prime 303053 := by norm_num
private theorem prime_fortyThreeAO_312527 : Nat.Prime 312527 := by norm_num
private theorem prime_fortyThreeAO_317969 : Nat.Prime 317969 := by norm_num
private theorem prime_fortyThreeAO_320053 : Nat.Prime 320053 := by norm_num
private theorem prime_fortyThreeAO_320291 : Nat.Prime 320291 := by norm_num
private theorem prime_fortyThreeAO_376417 : Nat.Prime 376417 := by norm_num
private theorem prime_fortyThreeAO_383297 : Nat.Prime 383297 := by norm_num
private theorem prime_fortyThreeAO_392069 : Nat.Prime 392069 := by norm_num
private theorem prime_fortyThreeAO_401587 : Nat.Prime 401587 := by norm_num
private theorem prime_fortyThreeAO_482117 : Nat.Prime 482117 := by norm_num
private theorem prime_fortyThreeAO_531383 : Nat.Prime 531383 := by norm_num
private theorem prime_fortyThreeAO_532709 : Nat.Prime 532709 := by norm_num
private theorem prime_fortyThreeAO_590929 : Nat.Prime 590929 := by norm_num
private theorem prime_fortyThreeAO_625861 : Nat.Prime 625861 := by norm_num
private theorem prime_fortyThreeAO_641833 : Nat.Prime 641833 := by norm_num
private theorem prime_fortyThreeAO_662227 : Nat.Prime 662227 := by norm_num
private theorem prime_fortyThreeAO_671123 : Nat.Prime 671123 := by norm_num
private theorem prime_fortyThreeAO_675341 : Nat.Prime 675341 := by norm_num
private theorem prime_fortyThreeAO_700027 : Nat.Prime 700027 := by norm_num
private theorem prime_fortyThreeAO_726013 : Nat.Prime 726013 := by norm_num
private theorem prime_fortyThreeAO_778541 : Nat.Prime 778541 := by norm_num
private theorem prime_fortyThreeAO_779981 : Nat.Prime 779981 := by norm_num
private theorem prime_fortyThreeAO_842267 : Nat.Prime 842267 := by norm_num
private theorem prime_fortyThreeAO_846721 : Nat.Prime 846721 := by norm_num
private theorem prime_fortyThreeAO_907793 : Nat.Prime 907793 := by norm_num
private theorem prime_fortyThreeAO_959947 : Nat.Prime 959947 := by norm_num
private theorem prime_fortyThreeAO_968027 : Nat.Prime 968027 := by norm_num
private theorem prime_fortyThreeAO_1012657 : Nat.Prime 1012657 := by norm_num
private theorem prime_fortyThreeAO_1180493 : Nat.Prime 1180493 := by norm_num
private theorem prime_fortyThreeAO_1282951 : Nat.Prime 1282951 := by norm_num
private theorem prime_fortyThreeAO_1327973 : Nat.Prime 1327973 := by norm_num
private theorem prime_fortyThreeAO_1366597 : Nat.Prime 1366597 := by norm_num
private theorem prime_fortyThreeAO_1432699 : Nat.Prime 1432699 := by norm_num
private theorem prime_fortyThreeAO_1467953 : Nat.Prime 1467953 := by norm_num
private theorem prime_fortyThreeAO_1578257 : Nat.Prime 1578257 := by norm_num
private theorem prime_fortyThreeAO_1608527 : Nat.Prime 1608527 := by norm_num
private theorem prime_fortyThreeAO_1613653 : Nat.Prime 1613653 := by norm_num
private theorem prime_fortyThreeAO_1627337 : Nat.Prime 1627337 := by norm_num
private theorem prime_fortyThreeAO_1653331 : Nat.Prime 1653331 := by norm_num
private theorem prime_fortyThreeAO_1673543 : Nat.Prime 1673543 := by norm_num
private theorem prime_fortyThreeAO_1800473 : Nat.Prime 1800473 := by norm_num
private theorem prime_fortyThreeAO_1889707 : Nat.Prime 1889707 := by norm_num
private theorem prime_fortyThreeAO_2123053 : Nat.Prime 2123053 := by norm_num
private theorem prime_fortyThreeAO_2233607 : Nat.Prime 2233607 := by norm_num
private theorem prime_fortyThreeAO_2270449 : Nat.Prime 2270449 := by norm_num
private theorem prime_fortyThreeAO_2450207 : Nat.Prime 2450207 := by norm_num
private theorem prime_fortyThreeAO_2455889 : Nat.Prime 2455889 := by norm_num
private theorem prime_fortyThreeAO_2715929 : Nat.Prime 2715929 := by norm_num
private theorem prime_fortyThreeAO_2873621 : Nat.Prime 2873621 := by norm_num
private theorem prime_fortyThreeAO_3016229 : Nat.Prime 3016229 := by norm_num
private theorem prime_fortyThreeAO_3176351 : Nat.Prime 3176351 := by norm_num
private theorem prime_fortyThreeAO_3473801 : Nat.Prime 3473801 := by norm_num
private theorem prime_fortyThreeAO_3582083 : Nat.Prime 3582083 := by norm_num
private theorem prime_fortyThreeAO_3615701 : Nat.Prime 3615701 := by norm_num
private theorem prime_fortyThreeAO_3644831 : Nat.Prime 3644831 := by norm_num
private theorem prime_fortyThreeAO_3681781 : Nat.Prime 3681781 := by norm_num
private theorem prime_fortyThreeAO_3824999 : Nat.Prime 3824999 := by norm_num
private theorem prime_fortyThreeAO_4647091 : Nat.Prime 4647091 := by norm_num
private theorem prime_fortyThreeAO_4963897 : Nat.Prime 4963897 := by norm_num
private theorem prime_fortyThreeAO_5041601 : Nat.Prime 5041601 := by norm_num
private theorem prime_fortyThreeAO_5047151 : Nat.Prime 5047151 := by norm_num
private theorem prime_fortyThreeAO_5252669 : Nat.Prime 5252669 := by norm_num
private theorem prime_fortyThreeAO_5651561 : Nat.Prime 5651561 := by norm_num
private theorem prime_fortyThreeAO_5927477 : Nat.Prime 5927477 := by norm_num
private theorem prime_fortyThreeAO_5943023 : Nat.Prime 5943023 := by norm_num
private theorem prime_fortyThreeAO_6111439 : Nat.Prime 6111439 := by norm_num
private theorem prime_fortyThreeAO_6313961 : Nat.Prime 6313961 := by norm_num
private theorem prime_fortyThreeAO_6489877 : Nat.Prime 6489877 := by norm_num
private theorem prime_fortyThreeAO_6700957 : Nat.Prime 6700957 := by norm_num
private theorem prime_fortyThreeAO_7001507 : Nat.Prime 7001507 := by norm_num
private theorem prime_fortyThreeAO_7014653 : Nat.Prime 7014653 := by norm_num
private theorem prime_fortyThreeAO_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_fortyThreeAO_7505249 : Nat.Prime 7505249 := by norm_num
private theorem prime_fortyThreeAO_7799453 : Nat.Prime 7799453 := by norm_num
private theorem prime_fortyThreeAO_8285363 : Nat.Prime 8285363 := by norm_num
private theorem prime_fortyThreeAO_8919161 : Nat.Prime 8919161 := by norm_num
private theorem prime_fortyThreeAO_9018263 : Nat.Prime 9018263 := by norm_num
private theorem prime_fortyThreeAO_9730229 : Nat.Prime 9730229 := by norm_num
private theorem prime_fortyThreeAO_9818671 : Nat.Prime 9818671 := by norm_num
private theorem prime_fortyThreeAO_11721217 : Nat.Prime 11721217 := by norm_num
private theorem prime_fortyThreeAO_12098971 : Nat.Prime 12098971 := by norm_num
private theorem prime_fortyThreeAO_12248567 : Nat.Prime 12248567 := by norm_num
private theorem prime_fortyThreeAO_15740909 : Nat.Prime 15740909 := by norm_num
private theorem prime_fortyThreeAO_15842063 : Nat.Prime 15842063 := by norm_num
private theorem prime_fortyThreeAO_16072387 : Nat.Prime 16072387 := by norm_num
private theorem prime_fortyThreeAO_16088077 : Nat.Prime 16088077 := by norm_num
private theorem prime_fortyThreeAO_16413157 : Nat.Prime 16413157 := by norm_num
private theorem prime_fortyThreeAO_17005033 : Nat.Prime 17005033 := by norm_num
private theorem prime_fortyThreeAO_18670303 : Nat.Prime 18670303 := by norm_num
private theorem prime_fortyThreeAO_18814171 : Nat.Prime 18814171 := by norm_num
private theorem prime_fortyThreeAO_19264327 : Nat.Prime 19264327 := by norm_num
private theorem prime_fortyThreeAO_19408331 : Nat.Prime 19408331 := by norm_num
private theorem prime_fortyThreeAO_21028771 : Nat.Prime 21028771 := by norm_num
private theorem prime_fortyThreeAO_21996109 : Nat.Prime 21996109 := by norm_num
private theorem prime_fortyThreeAO_22661333 : Nat.Prime 22661333 := by norm_num
private theorem prime_fortyThreeAO_24613591 : Nat.Prime 24613591 := by norm_num
private theorem prime_fortyThreeAO_25973737 : Nat.Prime 25973737 := by norm_num
private theorem prime_fortyThreeAO_26126017 : Nat.Prime 26126017 := by norm_num
private theorem prime_fortyThreeAO_26356279 : Nat.Prime 26356279 := by norm_num
private theorem prime_fortyThreeAO_26882591 : Nat.Prime 26882591 := by norm_num
private theorem prime_fortyThreeAO_28915153 : Nat.Prime 28915153 := by norm_num
private theorem prime_fortyThreeAO_29324153 : Nat.Prime 29324153 := by norm_num

private theorem prime_fortyThreeAO_31047293 : Nat.Prime 31047293 := by
  apply lucas_primality 31047293 (2 : ZMod 31047293)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (37, 1), (61, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (37, 1), (61, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) = 31047293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_37
      · exact prime_fortyThreeAO_61
      · exact prime_fortyThreeAO_181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31047293) ^ 15523646 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 31047293) ^ 1634068 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 31047293) ^ 839116 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 31047293) ^ 508972 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 31047293) ^ 171532 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_35383199 : Nat.Prime 35383199 := by
  apply lucas_primality 35383199 (11 : ZMod 35383199)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (376417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (376417, 1)] : List FactorBlock).map factorBlockValue).prod) = 35383199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_47
      · exact prime_fortyThreeAO_376417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 35383199) ^ 17691599 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 35383199) ^ 752834 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 35383199) ^ 94 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_36194749 : Nat.Prime 36194749 := by
  apply lucas_primality 36194749 (2 : ZMod 36194749)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3016229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3016229, 1)] : List FactorBlock).map factorBlockValue).prod) = 36194749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_3016229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36194749) ^ 18097374 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 36194749) ^ 12064916 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 36194749) ^ 12 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_41422313 : Nat.Prime 41422313 := by
  apply lucas_primality 41422313 (3 : ZMod 41422313)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (83, 1), (62383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (83, 1), (62383, 1)] : List FactorBlock).map factorBlockValue).prod) = 41422313 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_83
      · exact prime_fortyThreeAO_62383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 41422313) ^ 20711156 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 41422313) ^ 499064 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 41422313) ^ 664 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_43246387 : Nat.Prime 43246387 := by
  apply lucas_primality 43246387 (7 : ZMod 43246387)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (266953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (266953, 1)] : List FactorBlock).map factorBlockValue).prod) = 43246387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_266953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 43246387) ^ 21623193 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 43246387) ^ 14415462 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 43246387) ^ 162 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_43618901 : Nat.Prime 43618901 := by
  apply lucas_primality 43618901 (2 : ZMod 43618901)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (13, 2), (29, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (13, 2), (29, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) = 43618901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_89
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43618901) ^ 21809450 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 43618901) ^ 8723780 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 43618901) ^ 3355300 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 43618901) ^ 1504100 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 43618901) ^ 490100 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_43793137 : Nat.Prime 43793137 := by
  apply lucas_primality 43793137 (10 : ZMod 43793137)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (33791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (33791, 1)] : List FactorBlock).map factorBlockValue).prod) = 43793137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_33791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 43793137) ^ 21896568 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 43793137) ^ 14597712 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 43793137) ^ 1296 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_44959199 : Nat.Prime 44959199 := by
  apply lucas_primality 44959199 (23 : ZMod 44959199)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1429, 1), (15731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1429, 1), (15731, 1)] : List FactorBlock).map factorBlockValue).prod) = 44959199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_1429
      · exact prime_fortyThreeAO_15731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 44959199) ^ 22479599 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (23 : ZMod 44959199) ^ 31462 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (23 : ZMod 44959199) ^ 2858 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_50511689 : Nat.Prime 50511689 := by
  apply lucas_primality 50511689 (3 : ZMod 50511689)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (6313961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (6313961, 1)] : List FactorBlock).map factorBlockValue).prod) = 50511689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_6313961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 50511689) ^ 25255844 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 50511689) ^ 8 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_54950629 : Nat.Prime 54950629 := by
  apply lucas_primality 54950629 (11 : ZMod 54950629)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (157, 1), (29167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (157, 1), (29167, 1)] : List FactorBlock).map factorBlockValue).prod) = 54950629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_157
      · exact prime_fortyThreeAO_29167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 54950629) ^ 27475314 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 54950629) ^ 18316876 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 54950629) ^ 350004 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 54950629) ^ 1884 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_58734107 : Nat.Prime 58734107 := by
  apply lucas_primality 58734107 (2 : ZMod 58734107)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (1012657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (1012657, 1)] : List FactorBlock).map factorBlockValue).prod) = 58734107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_1012657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 58734107) ^ 29367053 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 58734107) ^ 2025314 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 58734107) ^ 58 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_60342517 : Nat.Prime 60342517 := by
  apply lucas_primality 60342517 (2 : ZMod 60342517)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (42979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (42979, 1)] : List FactorBlock).map factorBlockValue).prod) = 60342517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_42979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 60342517) ^ 30171258 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 60342517) ^ 20114172 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 60342517) ^ 4641732 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 60342517) ^ 1404 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_60456481 : Nat.Prime 60456481 := by
  apply lucas_primality 60456481 (11 : ZMod 60456481)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (7, 1), (19, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (7, 1), (19, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) = 60456481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 60456481) ^ 30228240 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 60456481) ^ 20152160 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 60456481) ^ 12091296 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 60456481) ^ 8636640 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 60456481) ^ 3181920 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 60456481) ^ 63840 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_69289013 : Nat.Prime 69289013 := by
  apply lucas_primality 69289013 (2 : ZMod 69289013)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (37, 1), (36013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (37, 1), (36013, 1)] : List FactorBlock).map factorBlockValue).prod) = 69289013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_37
      · exact prime_fortyThreeAO_36013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 69289013) ^ 34644506 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 69289013) ^ 5329924 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 69289013) ^ 1872676 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 69289013) ^ 1924 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_71481227 : Nat.Prime 71481227 := by
  apply lucas_primality 71481227 (5 : ZMod 71481227)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (31, 1), (67819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (31, 1), (67819, 1)] : List FactorBlock).map factorBlockValue).prod) = 71481227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_31
      · exact prime_fortyThreeAO_67819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 71481227) ^ 35740613 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 71481227) ^ 4204778 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 71481227) ^ 2305846 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 71481227) ^ 1054 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_74367413 : Nat.Prime 74367413 := by
  apply lucas_primality 74367413 (2 : ZMod 74367413)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (367, 1), (7237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (367, 1), (7237, 1)] : List FactorBlock).map factorBlockValue).prod) = 74367413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_367
      · exact prime_fortyThreeAO_7237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 74367413) ^ 37183706 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 74367413) ^ 10623916 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 74367413) ^ 202636 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 74367413) ^ 10276 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_77581919 : Nat.Prime 77581919 := by
  apply lucas_primality 77581919 (7 : ZMod 77581919)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (531383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (531383, 1)] : List FactorBlock).map factorBlockValue).prod) = 77581919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_73
      · exact prime_fortyThreeAO_531383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 77581919) ^ 38790959 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 77581919) ^ 1062766 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 77581919) ^ 146 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_81299501 : Nat.Prime 81299501 := by
  apply lucas_primality 81299501 (2 : ZMod 81299501)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (277, 1), (587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (277, 1), (587, 1)] : List FactorBlock).map factorBlockValue).prod) = 81299501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_277
      · exact prime_fortyThreeAO_587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 81299501) ^ 40649750 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 81299501) ^ 16259900 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 81299501) ^ 293500 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 81299501) ^ 138500 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_85709917 : Nat.Prime 85709917 := by
  apply lucas_primality 85709917 (2 : ZMod 85709917)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (31, 1), (76801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (31, 1), (76801, 1)] : List FactorBlock).map factorBlockValue).prod) = 85709917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_31
      · exact prime_fortyThreeAO_76801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 85709917) ^ 42854958 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 85709917) ^ 28569972 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 85709917) ^ 2764836 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 85709917) ^ 1116 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_89675291 : Nat.Prime 89675291 := by
  apply lucas_primality 89675291 (2 : ZMod 89675291)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (499, 1), (17971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (499, 1), (17971, 1)] : List FactorBlock).map factorBlockValue).prod) = 89675291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_499
      · exact prime_fortyThreeAO_17971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 89675291) ^ 44837645 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 89675291) ^ 17935058 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 89675291) ^ 179710 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 89675291) ^ 4990 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_91842479 : Nat.Prime 91842479 := by
  apply lucas_primality 91842479 (11 : ZMod 91842479)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (29, 1), (17401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (29, 1), (17401, 1)] : List FactorBlock).map factorBlockValue).prod) = 91842479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_17401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 91842479) ^ 45921239 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 91842479) ^ 13120354 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 91842479) ^ 7064806 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 91842479) ^ 3166982 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 91842479) ^ 5278 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_92562901 : Nat.Prime 92562901 := by
  apply lucas_primality 92562901 (10 : ZMod 92562901)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (31, 1), (37, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (31, 1), (37, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) = 92562901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_31
      · exact prime_fortyThreeAO_37
      · exact prime_fortyThreeAO_269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 92562901) ^ 46281450 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 92562901) ^ 30854300 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 92562901) ^ 18512580 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 92562901) ^ 2985900 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 92562901) ^ 2501700 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 92562901) ^ 344100 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_92984711 : Nat.Prime 92984711 := by
  apply lucas_primality 92984711 (7 : ZMod 92984711)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (102181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (102181, 1)] : List FactorBlock).map factorBlockValue).prod) = 92984711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_102181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 92984711) ^ 46492355 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 92984711) ^ 18596942 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 92984711) ^ 13283530 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 92984711) ^ 7152670 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 92984711) ^ 910 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_96528463 : Nat.Prime 96528463 := by
  apply lucas_primality 96528463 (3 : ZMod 96528463)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (16088077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (16088077, 1)] : List FactorBlock).map factorBlockValue).prod) = 96528463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_16088077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 96528463) ^ 48264231 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 96528463) ^ 32176154 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 96528463) ^ 6 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_102773491 : Nat.Prime 102773491 := by
  apply lucas_primality 102773491 (3 : ZMod 102773491)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (47, 1), (72889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (47, 1), (72889, 1)] : List FactorBlock).map factorBlockValue).prod) = 102773491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_47
      · exact prime_fortyThreeAO_72889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 102773491) ^ 51386745 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 102773491) ^ 34257830 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 102773491) ^ 20554698 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 102773491) ^ 2186670 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 102773491) ^ 1410 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_109119847 : Nat.Prime 109119847 := by
  apply lucas_primality 109119847 (3 : ZMod 109119847)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1653331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1653331, 1)] : List FactorBlock).map factorBlockValue).prod) = 109119847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_1653331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 109119847) ^ 54559923 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 109119847) ^ 36373282 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 109119847) ^ 9919986 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 109119847) ^ 66 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_112341631 : Nat.Prime 112341631 := by
  apply lucas_primality 112341631 (3 : ZMod 112341631)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (317, 1), (11813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (317, 1), (11813, 1)] : List FactorBlock).map factorBlockValue).prod) = 112341631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_317
      · exact prime_fortyThreeAO_11813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 112341631) ^ 56170815 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112341631) ^ 37447210 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112341631) ^ 22468326 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112341631) ^ 354390 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112341631) ^ 9510 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_112885027 : Nat.Prime 112885027 := by
  apply lucas_primality 112885027 (2 : ZMod 112885027)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (18814171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (18814171, 1)] : List FactorBlock).map factorBlockValue).prod) = 112885027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_18814171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 112885027) ^ 56442513 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 112885027) ^ 37628342 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 112885027) ^ 6 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_130281169 : Nat.Prime 130281169 := by
  apply lucas_primality 130281169 (13 : ZMod 130281169)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1069, 1), (2539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1069, 1), (2539, 1)] : List FactorBlock).map factorBlockValue).prod) = 130281169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_1069
      · exact prime_fortyThreeAO_2539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 130281169) ^ 65140584 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 130281169) ^ 43427056 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 130281169) ^ 121872 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 130281169) ^ 51312 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_147005671 : Nat.Prime 147005671 := by
  apply lucas_primality 147005671 (6 : ZMod 147005671)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (700027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (700027, 1)] : List FactorBlock).map factorBlockValue).prod) = 147005671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_700027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 147005671) ^ 73502835 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 147005671) ^ 49001890 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 147005671) ^ 29401134 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 147005671) ^ 21000810 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 147005671) ^ 210 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_153636319 : Nat.Prime 153636319 := by
  apply lucas_primality 153636319 (3 : ZMod 153636319)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (19, 1), (13613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (19, 1), (13613, 1)] : List FactorBlock).map factorBlockValue).prod) = 153636319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_13613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 153636319) ^ 76818159 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 153636319) ^ 51212106 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 153636319) ^ 13966938 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 153636319) ^ 8086122 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 153636319) ^ 11286 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_181411873 : Nat.Prime 181411873 := by
  apply lucas_primality 181411873 (5 : ZMod 181411873)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (1889707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (1889707, 1)] : List FactorBlock).map factorBlockValue).prod) = 181411873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_1889707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 181411873) ^ 90705936 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 181411873) ^ 60470624 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 181411873) ^ 96 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_184463687 : Nat.Prime 184463687 := by
  apply lucas_primality 184463687 (5 : ZMod 184463687)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (113, 1), (74201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (113, 1), (74201, 1)] : List FactorBlock).map factorBlockValue).prod) = 184463687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_113
      · exact prime_fortyThreeAO_74201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 184463687) ^ 92231843 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 184463687) ^ 16769426 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 184463687) ^ 1632422 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 184463687) ^ 2486 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_190069507 : Nat.Prime 190069507 := by
  apply lucas_primality 190069507 (2 : ZMod 190069507)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (959947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (959947, 1)] : List FactorBlock).map factorBlockValue).prod) = 190069507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_959947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 190069507) ^ 95034753 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 190069507) ^ 63356502 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 190069507) ^ 17279046 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 190069507) ^ 198 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_197593663 : Nat.Prime 197593663 := by
  apply lucas_primality 197593663 (6 : ZMod 197593663)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (811, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (811, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) = 197593663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_811
      · exact prime_fortyThreeAO_5801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 197593663) ^ 98796831 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 197593663) ^ 65864554 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 197593663) ^ 28227666 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 197593663) ^ 243642 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 197593663) ^ 34062 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_210439591 : Nat.Prime 210439591 := by
  apply lucas_primality 210439591 (3 : ZMod 210439591)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7014653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7014653, 1)] : List FactorBlock).map factorBlockValue).prod) = 210439591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7014653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 210439591) ^ 105219795 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 210439591) ^ 70146530 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 210439591) ^ 42087918 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 210439591) ^ 30 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_220372727 : Nat.Prime 220372727 := by
  apply lucas_primality 220372727 (5 : ZMod 220372727)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (15740909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (15740909, 1)] : List FactorBlock).map factorBlockValue).prod) = 220372727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_15740909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 220372727) ^ 110186363 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 220372727) ^ 31481818 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 220372727) ^ 14 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_225064031 : Nat.Prime 225064031 := by
  apply lucas_primality 225064031 (11 : ZMod 225064031)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (726013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (726013, 1)] : List FactorBlock).map factorBlockValue).prod) = 225064031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_31
      · exact prime_fortyThreeAO_726013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 225064031) ^ 112532015 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 225064031) ^ 45012806 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 225064031) ^ 7260130 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 225064031) ^ 310 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_240719249 : Nat.Prime 240719249 := by
  apply lucas_primality 240719249 (3 : ZMod 240719249)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (11, 1), (195389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (11, 1), (195389, 1)] : List FactorBlock).map factorBlockValue).prod) = 240719249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_195389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 240719249) ^ 120359624 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 240719249) ^ 34388464 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 240719249) ^ 21883568 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 240719249) ^ 1232 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_261301657 : Nat.Prime 261301657 := by
  apply lucas_primality 261301657 (5 : ZMod 261301657)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (141397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (141397, 1)] : List FactorBlock).map factorBlockValue).prod) = 261301657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_141397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 261301657) ^ 130650828 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 261301657) ^ 87100552 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 261301657) ^ 37328808 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 261301657) ^ 23754696 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 261301657) ^ 1848 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_312986969 : Nat.Prime 312986969 := by
  apply lucas_primality 312986969 (3 : ZMod 312986969)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (491, 1), (11383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (491, 1), (11383, 1)] : List FactorBlock).map factorBlockValue).prod) = 312986969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_491
      · exact prime_fortyThreeAO_11383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 312986969) ^ 156493484 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 312986969) ^ 44712424 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 312986969) ^ 637448 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 312986969) ^ 27496 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_411189901 : Nat.Prime 411189901 := by
  apply lucas_primality 411189901 (6 : ZMod 411189901)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (11, 1), (53, 1), (2351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (11, 1), (53, 1), (2351, 1)] : List FactorBlock).map factorBlockValue).prod) = 411189901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_53
      · exact prime_fortyThreeAO_2351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 411189901) ^ 205594950 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 411189901) ^ 137063300 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 411189901) ^ 82237980 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 411189901) ^ 37380900 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 411189901) ^ 7758300 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 411189901) ^ 174900 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_415352129 : Nat.Prime 415352129 := by
  apply lucas_primality 415352129 (3 : ZMod 415352129)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (6489877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (6489877, 1)] : List FactorBlock).map factorBlockValue).prod) = 415352129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_6489877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 415352129) ^ 207676064 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 415352129) ^ 64 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_434336989 : Nat.Prime 434336989 := by
  apply lucas_primality 434336989 (6 : ZMod 434336989)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (36194749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (36194749, 1)] : List FactorBlock).map factorBlockValue).prod) = 434336989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_36194749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 434336989) ^ 217168494 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 434336989) ^ 144778996 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 434336989) ^ 12 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_443044639 : Nat.Prime 443044639 := by
  apply lucas_primality 443044639 (3 : ZMod 443044639)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (24613591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (24613591, 1)] : List FactorBlock).map factorBlockValue).prod) = 443044639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_24613591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 443044639) ^ 221522319 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 443044639) ^ 147681546 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 443044639) ^ 18 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_477470633 : Nat.Prime 477470633 := by
  apply lucas_primality 477470633 (3 : ZMod 477470633)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (101, 1), (590929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (101, 1), (590929, 1)] : List FactorBlock).map factorBlockValue).prod) = 477470633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_101
      · exact prime_fortyThreeAO_590929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 477470633) ^ 238735316 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 477470633) ^ 4727432 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 477470633) ^ 808 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_483886639 : Nat.Prime 483886639 := by
  apply lucas_primality 483886639 (6 : ZMod 483886639)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (26882591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (26882591, 1)] : List FactorBlock).map factorBlockValue).prod) = 483886639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_26882591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 483886639) ^ 241943319 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 483886639) ^ 161295546 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 483886639) ^ 18 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_499324999 : Nat.Prime 499324999 := by
  apply lucas_primality 499324999 (15 : ZMod 499324999)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (157, 1), (17099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (157, 1), (17099, 1)] : List FactorBlock).map factorBlockValue).prod) = 499324999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_31
      · exact prime_fortyThreeAO_157
      · exact prime_fortyThreeAO_17099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 499324999) ^ 249662499 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (15 : ZMod 499324999) ^ 166441666 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (15 : ZMod 499324999) ^ 16107258 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (15 : ZMod 499324999) ^ 3180414 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (15 : ZMod 499324999) ^ 29202 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_505419127 : Nat.Prime 505419127 := by
  apply lucas_primality 505419127 (6 : ZMod 505419127)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (331, 1), (254491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (331, 1), (254491, 1)] : List FactorBlock).map factorBlockValue).prod) = 505419127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_331
      · exact prime_fortyThreeAO_254491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 505419127) ^ 252709563 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 505419127) ^ 168473042 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 505419127) ^ 1526946 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 505419127) ^ 1986 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_514476301 : Nat.Prime 514476301 := by
  apply lucas_primality 514476301 (2 : ZMod 514476301)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (13, 1), (19, 1), (53, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (13, 1), (19, 1), (53, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) = 514476301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_53
      · exact prime_fortyThreeAO_131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 514476301) ^ 257238150 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 514476301) ^ 171492100 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 514476301) ^ 102895260 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 514476301) ^ 39575100 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 514476301) ^ 27077700 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 514476301) ^ 9707100 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 514476301) ^ 3927300 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_527849863 : Nat.Prime 527849863 := by
  apply lucas_primality 527849863 (3 : ZMod 527849863)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (3824999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (3824999, 1)] : List FactorBlock).map factorBlockValue).prod) = 527849863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_3824999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 527849863) ^ 263924931 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 527849863) ^ 175949954 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 527849863) ^ 22949994 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 527849863) ^ 138 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_562563619 : Nat.Prime 562563619 := by
  apply lucas_primality 562563619 (3 : ZMod 562563619)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (499, 1), (187897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (499, 1), (187897, 1)] : List FactorBlock).map factorBlockValue).prod) = 562563619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_499
      · exact prime_fortyThreeAO_187897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 562563619) ^ 281281809 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 562563619) ^ 187521206 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 562563619) ^ 1127382 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 562563619) ^ 2994 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_630383263 : Nat.Prime 630383263 := by
  apply lucas_primality 630383263 (3 : ZMod 630383263)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (1180493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (1180493, 1)] : List FactorBlock).map factorBlockValue).prod) = 630383263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_89
      · exact prime_fortyThreeAO_1180493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 630383263) ^ 315191631 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 630383263) ^ 210127754 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 630383263) ^ 7082958 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 630383263) ^ 534 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_705149923 : Nat.Prime 705149923 := by
  apply lucas_primality 705149923 (7 : ZMod 705149923)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (3176351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (3176351, 1)] : List FactorBlock).map factorBlockValue).prod) = 705149923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_37
      · exact prime_fortyThreeAO_3176351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 705149923) ^ 352574961 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 705149923) ^ 235049974 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 705149923) ^ 19058106 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 705149923) ^ 222 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_756278437 : Nat.Prime 756278437 := by
  apply lucas_primality 756278437 (5 : ZMod 756278437)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (269, 1), (234287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (269, 1), (234287, 1)] : List FactorBlock).map factorBlockValue).prod) = 756278437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_269
      · exact prime_fortyThreeAO_234287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 756278437) ^ 378139218 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 756278437) ^ 252092812 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 756278437) ^ 2811444 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 756278437) ^ 3228 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_804444499 : Nat.Prime 804444499 := by
  apply lucas_primality 804444499 (2 : ZMod 804444499)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (13, 1), (312527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (13, 1), (312527, 1)] : List FactorBlock).map factorBlockValue).prod) = 804444499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_312527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 804444499) ^ 402222249 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 804444499) ^ 268148166 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 804444499) ^ 73131318 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 804444499) ^ 61880346 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 804444499) ^ 2574 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_852854719 : Nat.Prime 852854719 := by
  apply lucas_primality 852854719 (3 : ZMod 852854719)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1229, 1), (115657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1229, 1), (115657, 1)] : List FactorBlock).map factorBlockValue).prod) = 852854719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_1229
      · exact prime_fortyThreeAO_115657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 852854719) ^ 426427359 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 852854719) ^ 284284906 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 852854719) ^ 693942 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 852854719) ^ 7374 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_875720611 : Nat.Prime 875720611 := by
  apply lucas_primality 875720611 (2 : ZMod 875720611)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (9730229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (9730229, 1)] : List FactorBlock).map factorBlockValue).prod) = 875720611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_9730229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 875720611) ^ 437860305 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 875720611) ^ 291906870 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 875720611) ^ 175144122 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 875720611) ^ 90 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1073470369 : Nat.Prime 1073470369 := by
  apply lucas_primality 1073470369 (7 : ZMod 1073470369)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (109, 1), (102587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (109, 1), (102587, 1)] : List FactorBlock).map factorBlockValue).prod) = 1073470369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_109
      · exact prime_fortyThreeAO_102587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1073470369) ^ 536735184 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1073470369) ^ 357823456 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1073470369) ^ 9848352 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1073470369) ^ 10464 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1167364339 : Nat.Prime 1167364339 := by
  apply lucas_primality 1167364339 (2 : ZMod 1167364339)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (661, 1), (6007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (661, 1), (6007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1167364339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_661
      · exact prime_fortyThreeAO_6007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1167364339) ^ 583682169 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1167364339) ^ 389121446 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1167364339) ^ 166766334 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1167364339) ^ 1766058 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1167364339) ^ 194334 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_113
      · exact prime_fortyThreeAO_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1272927463 : Nat.Prime 1272927463 := by
  apply lucas_primality 1272927463 (11 : ZMod 1272927463)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (277, 1), (45053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (277, 1), (45053, 1)] : List FactorBlock).map factorBlockValue).prod) = 1272927463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_277
      · exact prime_fortyThreeAO_45053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1272927463) ^ 636463731 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 1272927463) ^ 424309154 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 1272927463) ^ 74878086 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 1272927463) ^ 4595406 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 1272927463) ^ 28254 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1285794707 : Nat.Prime 1285794707 := by
  apply lucas_primality 1285794707 (2 : ZMod 1285794707)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (91842479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (91842479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1285794707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_91842479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1285794707) ^ 642897353 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1285794707) ^ 183684958 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1285794707) ^ 14 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1299194657 : Nat.Prime 1299194657 := by
  apply lucas_primality 1299194657 (3 : ZMod 1299194657)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (1693, 1), (23981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (1693, 1), (23981, 1)] : List FactorBlock).map factorBlockValue).prod) = 1299194657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_1693
      · exact prime_fortyThreeAO_23981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1299194657) ^ 649597328 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1299194657) ^ 767392 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1299194657) ^ 54176 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1610610409 : Nat.Prime 1610610409 := by
  apply lucas_primality 1610610409 (13 : ZMod 1610610409)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (43, 1), (47293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (43, 1), (47293, 1)] : List FactorBlock).map factorBlockValue).prod) = 1610610409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_43
      · exact prime_fortyThreeAO_47293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1610610409) ^ 805305204 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 1610610409) ^ 536870136 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 1610610409) ^ 146419128 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 1610610409) ^ 37456056 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 1610610409) ^ 34056 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_2134222061 : Nat.Prime 2134222061 := by
  apply lucas_primality 2134222061 (2 : ZMod 2134222061)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (47, 1), (2270449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (47, 1), (2270449, 1)] : List FactorBlock).map factorBlockValue).prod) = 2134222061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_47
      · exact prime_fortyThreeAO_2270449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2134222061) ^ 1067111030 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2134222061) ^ 426844412 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2134222061) ^ 45408980 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2134222061) ^ 940 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_2269153009 : Nat.Prime 2269153009 := by
  apply lucas_primality 2269153009 (13 : ZMod 2269153009)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5252669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5252669, 1)] : List FactorBlock).map factorBlockValue).prod) = 2269153009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5252669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 2269153009) ^ 1134576504 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 2269153009) ^ 756384336 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 2269153009) ^ 432 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_2307926419 : Nat.Prime 2307926419 := by
  apply lucas_primality 2307926419 (3 : ZMod 2307926419)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (54950629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (54950629, 1)] : List FactorBlock).map factorBlockValue).prod) = 2307926419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_54950629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2307926419) ^ 1153963209 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2307926419) ^ 769308806 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2307926419) ^ 329703774 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2307926419) ^ 42 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_2352090737 : Nat.Prime 2352090737 := by
  apply lucas_primality 2352090737 (3 : ZMod 2352090737)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (147005671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (147005671, 1)] : List FactorBlock).map factorBlockValue).prod) = 2352090737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_147005671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2352090737) ^ 1176045368 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2352090737) ^ 16 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_2655507551 : Nat.Prime 2655507551 := by
  apply lucas_primality 2655507551 (11 : ZMod 2655507551)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (23, 1), (131, 1), (17627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (23, 1), (131, 1), (17627, 1)] : List FactorBlock).map factorBlockValue).prod) = 2655507551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_131
      · exact prime_fortyThreeAO_17627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2655507551) ^ 1327753775 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 2655507551) ^ 531101510 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 2655507551) ^ 115456850 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 2655507551) ^ 20271050 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 2655507551) ^ 150650 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_2686246397 : Nat.Prime 2686246397 := by
  apply lucas_primality 2686246397 (2 : ZMod 2686246397)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (5943023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (5943023, 1)] : List FactorBlock).map factorBlockValue).prod) = 2686246397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_113
      · exact prime_fortyThreeAO_5943023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2686246397) ^ 1343123198 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2686246397) ^ 23772092 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2686246397) ^ 452 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_3411418877 : Nat.Prime 3411418877 := by
  apply lucas_primality 3411418877 (2 : ZMod 3411418877)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (852854719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (852854719, 1)] : List FactorBlock).map factorBlockValue).prod) = 3411418877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_852854719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3411418877) ^ 1705709438 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3411418877) ^ 4 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_3897795203 : Nat.Prime 3897795203 := by
  apply lucas_primality 3897795203 (5 : ZMod 3897795203)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (61, 1), (163, 1), (28001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (61, 1), (163, 1), (28001, 1)] : List FactorBlock).map factorBlockValue).prod) = 3897795203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_61
      · exact prime_fortyThreeAO_163
      · exact prime_fortyThreeAO_28001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3897795203) ^ 1948897601 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3897795203) ^ 556827886 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3897795203) ^ 63898282 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3897795203) ^ 23912854 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3897795203) ^ 139202 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_4114076017 : Nat.Prime 4114076017 := by
  apply lucas_primality 4114076017 (5 : ZMod 4114076017)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (85709917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (85709917, 1)] : List FactorBlock).map factorBlockValue).prod) = 4114076017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_85709917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4114076017) ^ 2057038008 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4114076017) ^ 1371358672 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4114076017) ^ 48 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_4316486623 : Nat.Prime 4316486623 := by
  apply lucas_primality 4316486623 (3 : ZMod 4316486623)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (102773491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (102773491, 1)] : List FactorBlock).map factorBlockValue).prod) = 4316486623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_102773491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4316486623) ^ 2158243311 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4316486623) ^ 1438828874 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4316486623) ^ 616640946 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4316486623) ^ 42 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_5127905417 : Nat.Prime 5127905417 := by
  apply lucas_primality 5127905417 (3 : ZMod 5127905417)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (127, 1), (5047151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (127, 1), (5047151, 1)] : List FactorBlock).map factorBlockValue).prod) = 5127905417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_127
      · exact prime_fortyThreeAO_5047151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5127905417) ^ 2563952708 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5127905417) ^ 40377208 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5127905417) ^ 1016 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_5286347743 : Nat.Prime 5286347743 := by
  apply lucas_primality 5286347743 (3 : ZMod 5286347743)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (71, 1), (283, 1), (3373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (71, 1), (283, 1), (3373, 1)] : List FactorBlock).map factorBlockValue).prod) = 5286347743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_71
      · exact prime_fortyThreeAO_283
      · exact prime_fortyThreeAO_3373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5286347743) ^ 2643173871 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5286347743) ^ 1762115914 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5286347743) ^ 406642134 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5286347743) ^ 74455602 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5286347743) ^ 18679674 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5286347743) ^ 1567254 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_5523571987 : Nat.Prime 5523571987 := by
  apply lucas_primality 5523571987 (2 : ZMod 5523571987)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (257, 1), (3582083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (257, 1), (3582083, 1)] : List FactorBlock).map factorBlockValue).prod) = 5523571987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_257
      · exact prime_fortyThreeAO_3582083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5523571987) ^ 2761785993 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5523571987) ^ 1841190662 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5523571987) ^ 21492498 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5523571987) ^ 1542 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_6204369463 : Nat.Prime 6204369463 := by
  apply lucas_primality 6204369463 (3 : ZMod 6204369463)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (44959199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (44959199, 1)] : List FactorBlock).map factorBlockValue).prod) = 6204369463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_44959199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6204369463) ^ 3102184731 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6204369463) ^ 2068123154 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6204369463) ^ 269755194 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6204369463) ^ 138 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_6593037337 : Nat.Prime 6593037337 := by
  apply lucas_primality 6593037337 (5 : ZMod 6593037337)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5477, 1), (5573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5477, 1), (5573, 1)] : List FactorBlock).map factorBlockValue).prod) = 6593037337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5477
      · exact prime_fortyThreeAO_5573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6593037337) ^ 3296518668 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6593037337) ^ 2197679112 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6593037337) ^ 1203768 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6593037337) ^ 1183032 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_6905827909 : Nat.Prime 6905827909 := by
  apply lucas_primality 6905827909 (2 : ZMod 6905827909)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (89, 1), (197, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (89, 1), (197, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) = 6905827909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_89
      · exact prime_fortyThreeAO_197
      · exact prime_fortyThreeAO_521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6905827909) ^ 3452913954 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6905827909) ^ 2301942636 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6905827909) ^ 986546844 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6905827909) ^ 77593572 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6905827909) ^ 35054964 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6905827909) ^ 13254948 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_7273683217 : Nat.Prime 7273683217 := by
  apply lucas_primality 7273683217 (10 : ZMod 7273683217)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (50511689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (50511689, 1)] : List FactorBlock).map factorBlockValue).prod) = 7273683217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_50511689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 7273683217) ^ 3636841608 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 7273683217) ^ 2424561072 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 7273683217) ^ 144 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_8772435509 : Nat.Prime 8772435509 := by
  apply lucas_primality 8772435509 (2 : ZMod 8772435509)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (47, 1), (2455889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (47, 1), (2455889, 1)] : List FactorBlock).map factorBlockValue).prod) = 8772435509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_47
      · exact prime_fortyThreeAO_2455889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8772435509) ^ 4386217754 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8772435509) ^ 461707132 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8772435509) ^ 186647564 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8772435509) ^ 3572 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_9184216597 : Nat.Prime 9184216597 := by
  apply lucas_primality 9184216597 (2 : ZMod 9184216597)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (83, 1), (317969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (83, 1), (317969, 1)] : List FactorBlock).map factorBlockValue).prod) = 9184216597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_83
      · exact prime_fortyThreeAO_317969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9184216597) ^ 4592108298 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9184216597) ^ 3061405532 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9184216597) ^ 316697124 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9184216597) ^ 110653212 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9184216597) ^ 28884 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_9996062173 : Nat.Prime 9996062173 := by
  apply lucas_primality 9996062173 (2 : ZMod 9996062173)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (83, 1), (937, 1), (10711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (83, 1), (937, 1), (10711, 1)] : List FactorBlock).map factorBlockValue).prod) = 9996062173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_83
      · exact prime_fortyThreeAO_937
      · exact prime_fortyThreeAO_10711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9996062173) ^ 4998031086 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9996062173) ^ 3332020724 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9996062173) ^ 120434484 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9996062173) ^ 10668156 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9996062173) ^ 933252 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_10813897949 : Nat.Prime 10813897949 := by
  apply lucas_primality 10813897949 (2 : ZMod 10813897949)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 2), (23, 1), (97, 1), (599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 2), (23, 1), (97, 1), (599, 1)] : List FactorBlock).map factorBlockValue).prod) = 10813897949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_97
      · exact prime_fortyThreeAO_599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10813897949) ^ 5406948974 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10813897949) ^ 1544842564 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10813897949) ^ 636111644 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10813897949) ^ 470169476 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10813897949) ^ 111483484 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10813897949) ^ 18053252 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_11024031407 : Nat.Prime 11024031407 := by
  apply lucas_primality 11024031407 (5 : ZMod 11024031407)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (190069507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (190069507, 1)] : List FactorBlock).map factorBlockValue).prod) = 11024031407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_190069507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 11024031407) ^ 5512015703 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 11024031407) ^ 380139014 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 11024031407) ^ 58 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_11141154919 : Nat.Prime 11141154919 := by
  apply lucas_primality 11141154919 (3 : ZMod 11141154919)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (43, 1), (846721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (43, 1), (846721, 1)] : List FactorBlock).map factorBlockValue).prod) = 11141154919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_43
      · exact prime_fortyThreeAO_846721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11141154919) ^ 5570577459 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 11141154919) ^ 3713718306 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 11141154919) ^ 655362054 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 11141154919) ^ 259096626 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 11141154919) ^ 13158 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_11234187311 : Nat.Prime 11234187311 := by
  apply lucas_primality 11234187311 (7 : ZMod 11234187311)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (26126017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (26126017, 1)] : List FactorBlock).map factorBlockValue).prod) = 11234187311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_43
      · exact prime_fortyThreeAO_26126017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 11234187311) ^ 5617093655 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 11234187311) ^ 2246837462 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 11234187311) ^ 261260170 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 11234187311) ^ 430 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_12033177131 : Nat.Prime 12033177131 := by
  apply lucas_primality 12033177131 (2 : ZMod 12033177131)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (92562901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (92562901, 1)] : List FactorBlock).map factorBlockValue).prod) = 12033177131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_92562901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12033177131) ^ 6016588565 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 12033177131) ^ 2406635426 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 12033177131) ^ 925629010 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 12033177131) ^ 130 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_15292896763 : Nat.Prime 15292896763 := by
  apply lucas_primality 15292896763 (3 : ZMod 15292896763)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (41, 1), (151, 1), (2879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (41, 1), (151, 1), (2879, 1)] : List FactorBlock).map factorBlockValue).prod) = 15292896763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_41
      · exact prime_fortyThreeAO_151
      · exact prime_fortyThreeAO_2879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15292896763) ^ 7646448381 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 15292896763) ^ 5097632254 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 15292896763) ^ 1390263342 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 15292896763) ^ 1176376674 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 15292896763) ^ 372997482 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 15292896763) ^ 101277462 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 15292896763) ^ 5311878 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_15678099421 : Nat.Prime 15678099421 := by
  apply lucas_primality 15678099421 (2 : ZMod 15678099421)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (261301657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (261301657, 1)] : List FactorBlock).map factorBlockValue).prod) = 15678099421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_261301657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15678099421) ^ 7839049710 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 15678099421) ^ 5226033140 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 15678099421) ^ 3135619884 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 15678099421) ^ 60 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_15796748141 : Nat.Prime 15796748141 := by
  apply lucas_primality 15796748141 (2 : ZMod 15796748141)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (41, 1), (19264327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (41, 1), (19264327, 1)] : List FactorBlock).map factorBlockValue).prod) = 15796748141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_41
      · exact prime_fortyThreeAO_19264327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15796748141) ^ 7898374070 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 15796748141) ^ 3159349628 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 15796748141) ^ 385286540 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 15796748141) ^ 820 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_16075861309 : Nat.Prime 16075861309 := by
  apply lucas_primality 16075861309 (6 : ZMod 16075861309)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (83, 1), (163, 1), (2539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (83, 1), (163, 1), (2539, 1)] : List FactorBlock).map factorBlockValue).prod) = 16075861309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_83
      · exact prime_fortyThreeAO_163
      · exact prime_fortyThreeAO_2539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 16075861309) ^ 8037930654 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 16075861309) ^ 5358620436 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 16075861309) ^ 1236604716 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 16075861309) ^ 193685076 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 16075861309) ^ 98624916 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 16075861309) ^ 6331572 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_16367054503 : Nat.Prime 16367054503 := by
  apply lucas_primality 16367054503 (3 : ZMod 16367054503)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (587, 1), (4647091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (587, 1), (4647091, 1)] : List FactorBlock).map factorBlockValue).prod) = 16367054503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_587
      · exact prime_fortyThreeAO_4647091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 16367054503) ^ 8183527251 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 16367054503) ^ 5455684834 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 16367054503) ^ 27882546 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 16367054503) ^ 3522 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_17265946493 : Nat.Prime 17265946493 := by
  apply lucas_primality 17265946493 (2 : ZMod 17265946493)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4316486623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4316486623, 1)] : List FactorBlock).map factorBlockValue).prod) = 17265946493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_4316486623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 17265946493) ^ 8632973246 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 17265946493) ^ 4 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_19894216417 : Nat.Prime 19894216417 := by
  apply lucas_primality 19894216417 (5 : ZMod 19894216417)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (2083, 1), (99487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (2083, 1), (99487, 1)] : List FactorBlock).map factorBlockValue).prod) = 19894216417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_2083
      · exact prime_fortyThreeAO_99487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 19894216417) ^ 9947108208 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 19894216417) ^ 6631405472 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 19894216417) ^ 9550752 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 19894216417) ^ 199968 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_22468374623 : Nat.Prime 22468374623 := by
  apply lucas_primality 22468374623 (5 : ZMod 22468374623)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11234187311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11234187311, 1)] : List FactorBlock).map factorBlockValue).prod) = 22468374623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_11234187311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 22468374623) ^ 11234187311 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 22468374623) ^ 2 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_26085720623 : Nat.Prime 26085720623 := by
  apply lucas_primality 26085720623 (5 : ZMod 26085720623)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (59, 1), (17005033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (59, 1), (17005033, 1)] : List FactorBlock).map factorBlockValue).prod) = 26085720623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_59
      · exact prime_fortyThreeAO_17005033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 26085720623) ^ 13042860311 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 26085720623) ^ 2006593894 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 26085720623) ^ 442130858 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 26085720623) ^ 1534 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_36773829607 : Nat.Prime 36773829607 := by
  apply lucas_primality 36773829607 (3 : ZMod 36773829607)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (77581919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (77581919, 1)] : List FactorBlock).map factorBlockValue).prod) = 36773829607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_79
      · exact prime_fortyThreeAO_77581919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 36773829607) ^ 18386914803 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 36773829607) ^ 12257943202 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 36773829607) ^ 465491514 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 36773829607) ^ 474 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_47615986981 : Nat.Prime 47615986981 := by
  apply lucas_primality 47615986981 (6 : ZMod 47615986981)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (31, 1), (1451, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (31, 1), (1451, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod) = 47615986981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_31
      · exact prime_fortyThreeAO_1451
      · exact prime_fortyThreeAO_5881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 47615986981) ^ 23807993490 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 47615986981) ^ 15871995660 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 47615986981) ^ 9523197396 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 47615986981) ^ 1535999580 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 47615986981) ^ 32815980 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 47615986981) ^ 8096580 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_55623105977 : Nat.Prime 55623105977 := by
  apply lucas_primality 55623105977 (3 : ZMod 55623105977)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (211, 1), (1432699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (211, 1), (1432699, 1)] : List FactorBlock).map factorBlockValue).prod) = 55623105977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_211
      · exact prime_fortyThreeAO_1432699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 55623105977) ^ 27811552988 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 55623105977) ^ 2418395912 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 55623105977) ^ 263616616 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 55623105977) ^ 38824 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_64592563963 : Nat.Prime 64592563963 := by
  apply lucas_primality 64592563963 (2 : ZMod 64592563963)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (71, 1), (8919161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (71, 1), (8919161, 1)] : List FactorBlock).map factorBlockValue).prod) = 64592563963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_71
      · exact prime_fortyThreeAO_8919161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 64592563963) ^ 32296281981 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 64592563963) ^ 21530854654 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 64592563963) ^ 3799562586 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 64592563963) ^ 909754422 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 64592563963) ^ 7242 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_70179484073 : Nat.Prime 70179484073 := by
  apply lucas_primality 70179484073 (3 : ZMod 70179484073)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (8772435509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (8772435509, 1)] : List FactorBlock).map factorBlockValue).prod) = 70179484073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_8772435509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 70179484073) ^ 35089742036 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 70179484073) ^ 8 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_74253122269 : Nat.Prime 74253122269 := by
  apply lucas_primality 74253122269 (2 : ZMod 74253122269)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (29, 1), (16413157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (29, 1), (16413157, 1)] : List FactorBlock).map factorBlockValue).prod) = 74253122269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_16413157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 74253122269) ^ 37126561134 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 74253122269) ^ 24751040756 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 74253122269) ^ 5711778636 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 74253122269) ^ 2560452492 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 74253122269) ^ 4524 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_76563147329 : Nat.Prime 76563147329 := by
  apply lucas_primality 76563147329 (3 : ZMod 76563147329)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (241, 1), (4963897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (241, 1), (4963897, 1)] : List FactorBlock).map factorBlockValue).prod) = 76563147329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_241
      · exact prime_fortyThreeAO_4963897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 76563147329) ^ 38281573664 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 76563147329) ^ 317689408 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 76563147329) ^ 15424 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_79171501313 : Nat.Prime 79171501313 := by
  apply lucas_primality 79171501313 (3 : ZMod 79171501313)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (17, 1), (1637, 1), (11113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (17, 1), (1637, 1), (11113, 1)] : List FactorBlock).map factorBlockValue).prod) = 79171501313 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_1637
      · exact prime_fortyThreeAO_11113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 79171501313) ^ 39585750656 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 79171501313) ^ 4657147136 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 79171501313) ^ 48363776 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 79171501313) ^ 7124224 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_79977725327 : Nat.Prime 79977725327 := by
  apply lucas_primality 79977725327 (10 : ZMod 79977725327)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (239, 1), (503, 1), (1151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (239, 1), (503, 1), (1151, 1)] : List FactorBlock).map factorBlockValue).prod) = 79977725327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_239
      · exact prime_fortyThreeAO_503
      · exact prime_fortyThreeAO_1151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 79977725327) ^ 39988862663 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 79977725327) ^ 4704572078 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 79977725327) ^ 334634834 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 79977725327) ^ 159001442 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 79977725327) ^ 69485426 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_110186363501 : Nat.Prime 110186363501 := by
  apply lucas_primality 110186363501 (2 : ZMod 110186363501)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (220372727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (220372727, 1)] : List FactorBlock).map factorBlockValue).prod) = 110186363501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_220372727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 110186363501) ^ 55093181750 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 110186363501) ^ 22037272700 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 110186363501) ^ 500 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_129765930739 : Nat.Prime 129765930739 := by
  apply lucas_primality 129765930739 (2 : ZMod 129765930739)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3089, 1), (7001507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3089, 1), (7001507, 1)] : List FactorBlock).map factorBlockValue).prod) = 129765930739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_3089
      · exact prime_fortyThreeAO_7001507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 129765930739) ^ 64882965369 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 129765930739) ^ 43255310246 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 129765930739) ^ 42009042 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 129765930739) ^ 18534 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_144038198041 : Nat.Prime 144038198041 := by
  apply lucas_primality 144038198041 (14 : ZMod 144038198041)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (109119847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (109119847, 1)] : List FactorBlock).map factorBlockValue).prod) = 144038198041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_109119847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 144038198041) ^ 72019099020 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 144038198041) ^ 48012732680 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 144038198041) ^ 28807639608 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 144038198041) ^ 13094381640 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 144038198041) ^ 1320 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_150669350707 : Nat.Prime 150669350707 := by
  apply lucas_primality 150669350707 (2 : ZMod 150669350707)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (83, 1), (907, 1), (47653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (83, 1), (907, 1), (47653, 1)] : List FactorBlock).map factorBlockValue).prod) = 150669350707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_83
      · exact prime_fortyThreeAO_907
      · exact prime_fortyThreeAO_47653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 150669350707) ^ 75334675353 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 150669350707) ^ 50223116902 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 150669350707) ^ 21524192958 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 150669350707) ^ 1815293382 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 150669350707) ^ 166118358 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 150669350707) ^ 3161802 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_158343002627 : Nat.Prime 158343002627 := by
  apply lucas_primality 158343002627 (2 : ZMod 158343002627)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79171501313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79171501313, 1)] : List FactorBlock).map factorBlockValue).prod) = 158343002627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_79171501313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 158343002627) ^ 79171501313 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 158343002627) ^ 2 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_162162311681 : Nat.Prime 162162311681 := by
  apply lucas_primality 162162311681 (3 : ZMod 162162311681)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (5, 1), (4933, 1), (12841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (5, 1), (4933, 1), (12841, 1)] : List FactorBlock).map factorBlockValue).prod) = 162162311681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_4933
      · exact prime_fortyThreeAO_12841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 162162311681) ^ 81081155840 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 162162311681) ^ 32432462336 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 162162311681) ^ 32872960 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 162162311681) ^ 12628480 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_185964135557 : Nat.Prime 185964135557 := by
  apply lucas_primality 185964135557 (2 : ZMod 185964135557)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (769, 1), (60456481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (769, 1), (60456481, 1)] : List FactorBlock).map factorBlockValue).prod) = 185964135557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_769
      · exact prime_fortyThreeAO_60456481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 185964135557) ^ 92982067778 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 185964135557) ^ 241825924 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 185964135557) ^ 3076 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_236695299101 : Nat.Prime 236695299101 := by
  apply lucas_primality 236695299101 (2 : ZMod 236695299101)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (13, 2), (239, 1), (58601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (13, 2), (239, 1), (58601, 1)] : List FactorBlock).map factorBlockValue).prod) = 236695299101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_239
      · exact prime_fortyThreeAO_58601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 236695299101) ^ 118347649550 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 236695299101) ^ 47339059820 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 236695299101) ^ 18207330700 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 236695299101) ^ 990356900 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 236695299101) ^ 4039100 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_256364582137 : Nat.Prime 256364582137 := by
  apply lucas_primality 256364582137 (7 : ZMod 256364582137)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (19, 1), (43246387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (19, 1), (43246387, 1)] : List FactorBlock).map factorBlockValue).prod) = 256364582137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_43246387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 256364582137) ^ 128182291068 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 256364582137) ^ 85454860712 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 256364582137) ^ 19720352472 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 256364582137) ^ 13492872744 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 256364582137) ^ 5928 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_365200088723 : Nat.Prime 365200088723 := by
  apply lucas_primality 365200088723 (2 : ZMod 365200088723)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (26085720623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (26085720623, 1)] : List FactorBlock).map factorBlockValue).prod) = 365200088723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_26085720623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 365200088723) ^ 182600044361 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 365200088723) ^ 52171441246 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 365200088723) ^ 14 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_387706153997 : Nat.Prime 387706153997 := by
  apply lucas_primality 387706153997 (2 : ZMod 387706153997)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (477470633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (477470633, 1)] : List FactorBlock).map factorBlockValue).prod) = 387706153997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_477470633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 387706153997) ^ 193853076998 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 387706153997) ^ 55386593428 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 387706153997) ^ 13369177724 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 387706153997) ^ 812 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_397
      · exact prime_fortyThreeAO_2531
      · exact prime_fortyThreeAO_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_471805563023 : Nat.Prime 471805563023 := by
  apply lucas_primality 471805563023 (5 : ZMod 471805563023)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (59, 1), (210439591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (59, 1), (210439591, 1)] : List FactorBlock).map factorBlockValue).prod) = 471805563023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_59
      · exact prime_fortyThreeAO_210439591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 471805563023) ^ 235902781511 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 471805563023) ^ 24831871738 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 471805563023) ^ 7996704458 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 471805563023) ^ 2242 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_571906676063 : Nat.Prime 571906676063 := by
  apply lucas_primality 571906676063 (5 : ZMod 571906676063)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (181183, 1), (1578257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (181183, 1), (1578257, 1)] : List FactorBlock).map factorBlockValue).prod) = 571906676063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_181183
      · exact prime_fortyThreeAO_1578257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 571906676063) ^ 285953338031 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 571906676063) ^ 3156514 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 571906676063) ^ 362366 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_587563074971 : Nat.Prime 587563074971 := by
  apply lucas_primality 587563074971 (2 : ZMod 587563074971)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (821, 1), (1499, 1), (47743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (821, 1), (1499, 1), (47743, 1)] : List FactorBlock).map factorBlockValue).prod) = 587563074971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_821
      · exact prime_fortyThreeAO_1499
      · exact prime_fortyThreeAO_47743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 587563074971) ^ 293781537485 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 587563074971) ^ 117512614994 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 587563074971) ^ 715667570 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 587563074971) ^ 391970030 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 587563074971) ^ 12306790 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_588381273713 : Nat.Prime 588381273713 := by
  apply lucas_primality 588381273713 (3 : ZMod 588381273713)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (36773829607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (36773829607, 1)] : List FactorBlock).map factorBlockValue).prod) = 588381273713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_36773829607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 588381273713) ^ 294190636856 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 588381273713) ^ 16 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_599580707419 : Nat.Prime 599580707419 := by
  apply lucas_primality 599580707419 (2 : ZMod 599580707419)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 2), (137, 1), (287059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 2), (137, 1), (287059, 1)] : List FactorBlock).map factorBlockValue).prod) = 599580707419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_137
      · exact prime_fortyThreeAO_287059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 599580707419) ^ 299790353709 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 599580707419) ^ 199860235806 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 599580707419) ^ 85654386774 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 599580707419) ^ 54507337038 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 599580707419) ^ 4376501514 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 599580707419) ^ 2088702 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_639821802617 : Nat.Prime 639821802617 := by
  apply lucas_primality 639821802617 (3 : ZMod 639821802617)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (79977725327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (79977725327, 1)] : List FactorBlock).map factorBlockValue).prod) = 639821802617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_79977725327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 639821802617) ^ 319910901308 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 639821802617) ^ 8 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_834987555011 : Nat.Prime 834987555011 := by
  apply lucas_primality 834987555011 (2 : ZMod 834987555011)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (53, 1), (225064031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (53, 1), (225064031, 1)] : List FactorBlock).map factorBlockValue).prod) = 834987555011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_53
      · exact prime_fortyThreeAO_225064031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 834987555011) ^ 417493777505 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 834987555011) ^ 166997511002 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 834987555011) ^ 119283936430 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 834987555011) ^ 15754482170 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 834987555011) ^ 3710 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_835354000651 : Nat.Prime 835354000651 := by
  apply lucas_primality 835354000651 (2 : ZMod 835354000651)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (13, 1), (5437, 1), (78791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (13, 1), (5437, 1), (78791, 1)] : List FactorBlock).map factorBlockValue).prod) = 835354000651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_5437
      · exact prime_fortyThreeAO_78791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 835354000651) ^ 417677000325 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 835354000651) ^ 278451333550 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 835354000651) ^ 167070800130 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 835354000651) ^ 64258000050 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 835354000651) ^ 153642450 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 835354000651) ^ 10602150 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1026270299401 : Nat.Prime 1026270299401 := by
  apply lucas_primality 1026270299401 (44 : ZMod 1026270299401)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (23, 1), (74367413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (23, 1), (74367413, 1)] : List FactorBlock).map factorBlockValue).prod) = 1026270299401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_74367413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (44 : ZMod 1026270299401) ^ 513135149700 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (44 : ZMod 1026270299401) ^ 342090099800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (44 : ZMod 1026270299401) ^ 205254059880 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (44 : ZMod 1026270299401) ^ 44620447800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (44 : ZMod 1026270299401) ^ 13800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1115784813343 : Nat.Prime 1115784813343 := by
  apply lucas_primality 1115784813343 (3 : ZMod 1115784813343)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (185964135557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (185964135557, 1)] : List FactorBlock).map factorBlockValue).prod) = 1115784813343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_185964135557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1115784813343) ^ 557892406671 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1115784813343) ^ 371928271114 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1115784813343) ^ 6 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1269398055311 : Nat.Prime 1269398055311 := by
  apply lucas_primality 1269398055311 (7 : ZMod 1269398055311)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (607, 1), (2715929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (607, 1), (2715929, 1)] : List FactorBlock).map factorBlockValue).prod) = 1269398055311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_607
      · exact prime_fortyThreeAO_2715929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1269398055311) ^ 634699027655 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1269398055311) ^ 253879611062 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1269398055311) ^ 181342579330 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1269398055311) ^ 115399823210 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1269398055311) ^ 2091265330 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1269398055311) ^ 467390 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1432795928341 : Nat.Prime 1432795928341 := by
  apply lucas_primality 1432795928341 (2 : ZMod 1432795928341)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (3411418877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (3411418877, 1)] : List FactorBlock).map factorBlockValue).prod) = 1432795928341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_3411418877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1432795928341) ^ 716397964170 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1432795928341) ^ 477598642780 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1432795928341) ^ 286559185668 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1432795928341) ^ 204685132620 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1432795928341) ^ 420 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1469474655521 : Nat.Prime 1469474655521 := by
  apply lucas_primality 1469474655521 (3 : ZMod 1469474655521)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (9184216597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (9184216597, 1)] : List FactorBlock).map factorBlockValue).prod) = 1469474655521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_9184216597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1469474655521) ^ 734737327760 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1469474655521) ^ 293894931104 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1469474655521) ^ 160 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_35279
      · exact prime_fortyThreeAO_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_2712887686447 : Nat.Prime 2712887686447 := by
  apply lucas_primality 2712887686447 (3 : ZMod 2712887686447)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (64592563963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (64592563963, 1)] : List FactorBlock).map factorBlockValue).prod) = 2712887686447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_64592563963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2712887686447) ^ 1356443843223 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2712887686447) ^ 904295895482 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2712887686447) ^ 387555383778 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2712887686447) ^ 42 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_3166860052541 : Nat.Prime 3166860052541 := by
  apply lucas_primality 3166860052541 (2 : ZMod 3166860052541)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (158343002627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (158343002627, 1)] : List FactorBlock).map factorBlockValue).prod) = 3166860052541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_158343002627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3166860052541) ^ 1583430026270 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3166860052541) ^ 633372010508 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3166860052541) ^ 20 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_3473595809543 : Nat.Prime 3473595809543 := by
  apply lucas_primality 3473595809543 (5 : ZMod 3473595809543)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (487, 1), (2131, 1), (1673543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (487, 1), (2131, 1), (1673543, 1)] : List FactorBlock).map factorBlockValue).prod) = 3473595809543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_487
      · exact prime_fortyThreeAO_2131
      · exact prime_fortyThreeAO_1673543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3473595809543) ^ 1736797904771 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3473595809543) ^ 7132640266 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3473595809543) ^ 1630030882 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3473595809543) ^ 2075594 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_4457754116957 : Nat.Prime 4457754116957 := by
  apply lucas_primality 4457754116957 (2 : ZMod 4457754116957)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (283, 1), (562563619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (283, 1), (562563619, 1)] : List FactorBlock).map factorBlockValue).prod) = 4457754116957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_283
      · exact prime_fortyThreeAO_562563619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4457754116957) ^ 2228877058478 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4457754116957) ^ 636822016708 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4457754116957) ^ 15751781332 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4457754116957) ^ 7924 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_5992522211239 : Nat.Prime 5992522211239 := by
  apply lucas_primality 5992522211239 (13 : ZMod 5992522211239)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (12033177131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (12033177131, 1)] : List FactorBlock).map factorBlockValue).prod) = 5992522211239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_83
      · exact prime_fortyThreeAO_12033177131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 5992522211239) ^ 2996261105619 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 5992522211239) ^ 1997507403746 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 5992522211239) ^ 72199062786 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 5992522211239) ^ 498 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_6067698961957 : Nat.Prime 6067698961957 := by
  apply lucas_primality 6067698961957 (11 : ZMod 6067698961957)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (179, 1), (241, 1), (11721217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (179, 1), (241, 1), (11721217, 1)] : List FactorBlock).map factorBlockValue).prod) = 6067698961957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_179
      · exact prime_fortyThreeAO_241
      · exact prime_fortyThreeAO_11721217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 6067698961957) ^ 3033849480978 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 6067698961957) ^ 2022566320652 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 6067698961957) ^ 33897759564 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 6067698961957) ^ 25177174116 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 6067698961957) ^ 517668 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_6725840978347 : Nat.Prime 6725840978347 := by
  apply lucas_primality 6725840978347 (2 : ZMod 6725840978347)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (79, 1), (3061, 1), (662227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (79, 1), (3061, 1), (662227, 1)] : List FactorBlock).map factorBlockValue).prod) = 6725840978347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_79
      · exact prime_fortyThreeAO_3061
      · exact prime_fortyThreeAO_662227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6725840978347) ^ 3362920489173 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6725840978347) ^ 2241946992782 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6725840978347) ^ 960834425478 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6725840978347) ^ 85137227574 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6725840978347) ^ 2197269186 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6725840978347) ^ 10156398 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_10223853786983 : Nat.Prime 10223853786983 := by
  apply lucas_primality 10223853786983 (5 : ZMod 10223853786983)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (173, 1), (2686246397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (173, 1), (2686246397, 1)] : List FactorBlock).map factorBlockValue).prod) = 10223853786983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_173
      · exact prime_fortyThreeAO_2686246397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10223853786983) ^ 5111926893491 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 10223853786983) ^ 929441253362 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 10223853786983) ^ 59097420734 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 10223853786983) ^ 3806 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_10829756568287 : Nat.Prime 10829756568287 := by
  apply lucas_primality 10829756568287 (5 : ZMod 10829756568287)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (241, 1), (22468374623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (241, 1), (22468374623, 1)] : List FactorBlock).map factorBlockValue).prod) = 10829756568287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_241
      · exact prime_fortyThreeAO_22468374623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 10829756568287) ^ 5414878284143 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 10829756568287) ^ 44936749246 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 10829756568287) ^ 482 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_10966707908617 : Nat.Prime 10966707908617 := by
  apply lucas_primality 10966707908617 (5 : ZMod 10966707908617)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (15803, 1), (28915153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (15803, 1), (28915153, 1)] : List FactorBlock).map factorBlockValue).prod) = 10966707908617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_15803
      · exact prime_fortyThreeAO_28915153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10966707908617) ^ 5483353954308 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 10966707908617) ^ 3655569302872 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 10966707908617) ^ 693963672 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 10966707908617) ^ 379272 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_15218545638187 : Nat.Prime 15218545638187 := by
  apply lucas_primality 15218545638187 (5 : ZMod 15218545638187)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (109, 1), (705149923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (109, 1), (705149923, 1)] : List FactorBlock).map factorBlockValue).prod) = 15218545638187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_109
      · exact prime_fortyThreeAO_705149923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 15218545638187) ^ 7609272819093 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 15218545638187) ^ 5072848546062 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 15218545638187) ^ 1383504148926 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 15218545638187) ^ 139619684754 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 15218545638187) ^ 21582 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_15846091487381 : Nat.Prime 15846091487381 := by
  apply lucas_primality 15846091487381 (2 : ZMod 15846091487381)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (11, 2), (59, 1), (2879, 1), (5507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (11, 2), (59, 1), (2879, 1), (5507, 1)] : List FactorBlock).map factorBlockValue).prod) = 15846091487381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_59
      · exact prime_fortyThreeAO_2879
      · exact prime_fortyThreeAO_5507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15846091487381) ^ 7923045743690 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 15846091487381) ^ 3169218297476 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 15846091487381) ^ 2263727355340 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 15846091487381) ^ 1440553771580 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 15846091487381) ^ 268577821820 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 15846091487381) ^ 5504026220 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 15846091487381) ^ 2877445340 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_21492071870237 : Nat.Prime 21492071870237 := by
  apply lucas_primality 21492071870237 (2 : ZMod 21492071870237)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (54163, 1), (9018263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (54163, 1), (9018263, 1)] : List FactorBlock).map factorBlockValue).prod) = 21492071870237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_54163
      · exact prime_fortyThreeAO_9018263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21492071870237) ^ 10746035935118 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 21492071870237) ^ 1953824715476 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 21492071870237) ^ 396803572 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 21492071870237) ^ 2383172 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_23780988279439 : Nat.Prime 23780988279439 := by
  apply lucas_primality 23780988279439 (6 : ZMod 23780988279439)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (379, 1), (804444499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (379, 1), (804444499, 1)] : List FactorBlock).map factorBlockValue).prod) = 23780988279439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_379
      · exact prime_fortyThreeAO_804444499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 23780988279439) ^ 11890494139719 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 23780988279439) ^ 7926996093146 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 23780988279439) ^ 1829306790726 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 23780988279439) ^ 62746670922 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 23780988279439) ^ 29562 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_25163893746773 : Nat.Prime 25163893746773 := by
  apply lucas_primality 25163893746773 (2 : ZMod 25163893746773)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (571906676063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (571906676063, 1)] : List FactorBlock).map factorBlockValue).prod) = 25163893746773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_571906676063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 25163893746773) ^ 12581946873386 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 25163893746773) ^ 2287626704252 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 25163893746773) ^ 44 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_25799065421539 : Nat.Prime 25799065421539 := by
  apply lucas_primality 25799065421539 (3 : ZMod 25799065421539)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (359, 1), (630383263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (359, 1), (630383263, 1)] : List FactorBlock).map factorBlockValue).prod) = 25799065421539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_359
      · exact prime_fortyThreeAO_630383263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 25799065421539) ^ 12899532710769 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 25799065421539) ^ 8599688473846 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 25799065421539) ^ 1357845548502 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 25799065421539) ^ 71863691982 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 25799065421539) ^ 40926 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_26213782231913 : Nat.Prime 26213782231913 := by
  apply lucas_primality 26213782231913 (3 : ZMod 26213782231913)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (19, 1), (15678099421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (19, 1), (15678099421, 1)] : List FactorBlock).map factorBlockValue).prod) = 26213782231913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_15678099421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26213782231913) ^ 13106891115956 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 26213782231913) ^ 2383071111992 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 26213782231913) ^ 1379672749048 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 26213782231913) ^ 1672 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_27766963602253 : Nat.Prime 27766963602253 := by
  apply lucas_primality 27766963602253 (6 : ZMod 27766963602253)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (110186363501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (110186363501, 1)] : List FactorBlock).map factorBlockValue).prod) = 27766963602253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_110186363501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 27766963602253) ^ 13883481801126 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 27766963602253) ^ 9255654534084 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 27766963602253) ^ 3966709086036 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 27766963602253) ^ 252 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_33220292875087 : Nat.Prime 33220292875087 := by
  apply lucas_primality 33220292875087 (5 : ZMod 33220292875087)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2399, 1), (2307926419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2399, 1), (2307926419, 1)] : List FactorBlock).map factorBlockValue).prod) = 33220292875087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_2399
      · exact prime_fortyThreeAO_2307926419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33220292875087) ^ 16610146437543 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 33220292875087) ^ 11073430958362 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 33220292875087) ^ 13847558514 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 33220292875087) ^ 14394 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_35065921476683 : Nat.Prime 35065921476683 := by
  apply lucas_primality 35065921476683 (2 : ZMod 35065921476683)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (229, 1), (76563147329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (229, 1), (76563147329, 1)] : List FactorBlock).map factorBlockValue).prod) = 35065921476683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_229
      · exact prime_fortyThreeAO_76563147329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35065921476683) ^ 17532960738341 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 35065921476683) ^ 153126294658 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 35065921476683) ^ 458 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_43034175312577 : Nat.Prime 43034175312577 := by
  apply lucas_primality 43034175312577 (10 : ZMod 43034175312577)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (29, 1), (25357, 1), (43543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (29, 1), (25357, 1), (43543, 1)] : List FactorBlock).map factorBlockValue).prod) = 43034175312577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_25357
      · exact prime_fortyThreeAO_43543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 43034175312577) ^ 21517087656288 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 43034175312577) ^ 14344725104192 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 43034175312577) ^ 6147739330368 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 43034175312577) ^ 1483937079744 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 43034175312577) ^ 1697131968 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 43034175312577) ^ 988314432 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_50077404703553 : Nat.Prime 50077404703553 := by
  apply lucas_primality 50077404703553 (3 : ZMod 50077404703553)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (83, 1), (499, 1), (1123, 1), (16823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (83, 1), (499, 1), (1123, 1), (16823, 1)] : List FactorBlock).map factorBlockValue).prod) = 50077404703553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_83
      · exact prime_fortyThreeAO_499
      · exact prime_fortyThreeAO_1123
      · exact prime_fortyThreeAO_16823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 50077404703553) ^ 25038702351776 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 50077404703553) ^ 603342225344 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 50077404703553) ^ 100355520448 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 50077404703553) ^ 44592524224 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 50077404703553) ^ 2976722624 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_54654067929823 : Nat.Prime 54654067929823 := by
  apply lucas_primality 54654067929823 (5 : ZMod 54654067929823)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5021, 1), (8123, 1), (223339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5021, 1), (8123, 1), (223339, 1)] : List FactorBlock).map factorBlockValue).prod) = 54654067929823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5021
      · exact prime_fortyThreeAO_8123
      · exact prime_fortyThreeAO_223339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 54654067929823) ^ 27327033964911 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 54654067929823) ^ 18218022643274 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 54654067929823) ^ 10885096182 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 54654067929823) ^ 6728310714 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 54654067929823) ^ 244713498 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_56908559640929 : Nat.Prime 56908559640929 := by
  apply lucas_primality 56908559640929 (3 : ZMod 56908559640929)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (103, 1), (17265946493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (103, 1), (17265946493, 1)] : List FactorBlock).map factorBlockValue).prod) = 56908559640929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_103
      · exact prime_fortyThreeAO_17265946493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 56908559640929) ^ 28454279820464 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 56908559640929) ^ 552510287776 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 56908559640929) ^ 3296 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_60596325868877 : Nat.Prime 60596325868877 := by
  apply lucas_primality 60596325868877 (2 : ZMod 60596325868877)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (137, 1), (15796748141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (137, 1), (15796748141, 1)] : List FactorBlock).map factorBlockValue).prod) = 60596325868877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_137
      · exact prime_fortyThreeAO_15796748141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 60596325868877) ^ 30298162934438 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 60596325868877) ^ 8656617981268 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 60596325868877) ^ 442308947948 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 60596325868877) ^ 3836 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_63337201050821 : Nat.Prime 63337201050821 := by
  apply lucas_primality 63337201050821 (2 : ZMod 63337201050821)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3166860052541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3166860052541, 1)] : List FactorBlock).map factorBlockValue).prod) = 63337201050821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_3166860052541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 63337201050821) ^ 31668600525410 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 63337201050821) ^ 12667440210164 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 63337201050821) ^ 20 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_66873845172377 : Nat.Prime 66873845172377 := by
  apply lucas_primality 66873845172377 (3 : ZMod 66873845172377)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (19, 1), (307, 1), (130281169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (19, 1), (307, 1), (130281169, 1)] : List FactorBlock).map factorBlockValue).prod) = 66873845172377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_307
      · exact prime_fortyThreeAO_130281169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 66873845172377) ^ 33436922586188 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 66873845172377) ^ 6079440470216 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 66873845172377) ^ 3519676061704 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 66873845172377) ^ 217830114568 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 66873845172377) ^ 513304 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_73641797680639 : Nat.Prime 73641797680639 := by
  apply lucas_primality 73641797680639 (11 : ZMod 73641797680639)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1115784813343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1115784813343, 1)] : List FactorBlock).map factorBlockValue).prod) = 73641797680639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_1115784813343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 73641797680639) ^ 36820898840319 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 73641797680639) ^ 24547265893546 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 73641797680639) ^ 6694708880058 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 73641797680639) ^ 66 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_94440542562361 : Nat.Prime 94440542562361 := by
  apply lucas_primality 94440542562361 (11 : ZMod 94440542562361)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (17, 1), (37, 1), (1033, 1), (134581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (17, 1), (37, 1), (1033, 1), (134581, 1)] : List FactorBlock).map factorBlockValue).prod) = 94440542562361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_37
      · exact prime_fortyThreeAO_1033
      · exact prime_fortyThreeAO_134581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 94440542562361) ^ 47220271281180 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 94440542562361) ^ 31480180854120 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 94440542562361) ^ 18888108512472 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 94440542562361) ^ 5555326033080 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 94440542562361) ^ 2552447096280 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 94440542562361) ^ 91423564920 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 94440542562361) ^ 701737560 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_121804629060419 : Nat.Prime 121804629060419 := by
  apply lucas_primality 121804629060419 (2 : ZMod 121804629060419)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (379, 1), (2663, 1), (60342517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (379, 1), (2663, 1), (60342517, 1)] : List FactorBlock).map factorBlockValue).prod) = 121804629060419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_379
      · exact prime_fortyThreeAO_2663
      · exact prime_fortyThreeAO_60342517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 121804629060419) ^ 60902314530209 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 121804629060419) ^ 321384245542 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 121804629060419) ^ 45739627886 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 121804629060419) ^ 2018554 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_135765237816139 : Nat.Prime 135765237816139 := by
  apply lucas_primality 135765237816139 (10 : ZMod 135765237816139)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1429, 1), (8543, 1), (264787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1429, 1), (8543, 1), (264787, 1)] : List FactorBlock).map factorBlockValue).prod) = 135765237816139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_1429
      · exact prime_fortyThreeAO_8543
      · exact prime_fortyThreeAO_264787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 135765237816139) ^ 67882618908069 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 135765237816139) ^ 45255079272046 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 135765237816139) ^ 19395033973734 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 135765237816139) ^ 95007164322 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 135765237816139) ^ 15891986166 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 135765237816139) ^ 512733774 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_138668764108067 : Nat.Prime 138668764108067 := by
  apply lucas_primality 138668764108067 (2 : ZMod 138668764108067)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (835354000651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (835354000651, 1)] : List FactorBlock).map factorBlockValue).prod) = 138668764108067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_83
      · exact prime_fortyThreeAO_835354000651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 138668764108067) ^ 69334382054033 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 138668764108067) ^ 1670708001302 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 138668764108067) ^ 166 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_167790621914693 : Nat.Prime 167790621914693 := by
  apply lucas_primality 167790621914693 (2 : ZMod 167790621914693)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (5992522211239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (5992522211239, 1)] : List FactorBlock).map factorBlockValue).prod) = 167790621914693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_5992522211239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 167790621914693) ^ 83895310957346 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 167790621914693) ^ 23970088844956 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 167790621914693) ^ 28 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_191964326140553 : Nat.Prime 191964326140553 := by
  apply lucas_primality 191964326140553 (3 : ZMod 191964326140553)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (29, 1), (130211, 1), (907793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (29, 1), (130211, 1), (907793, 1)] : List FactorBlock).map factorBlockValue).prod) = 191964326140553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_130211
      · exact prime_fortyThreeAO_907793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 191964326140553) ^ 95982163070276 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 191964326140553) ^ 27423475162936 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 191964326140553) ^ 6619459522088 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 191964326140553) ^ 1474255832 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 191964326140553) ^ 211462664 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_329209064005537 : Nat.Prime 329209064005537 := by
  apply lucas_primality 329209064005537 (15 : ZMod 329209064005537)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (11, 1), (13, 1), (233, 1), (877, 1), (39119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (11, 1), (13, 1), (233, 1), (877, 1), (39119, 1)] : List FactorBlock).map factorBlockValue).prod) = 329209064005537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_233
      · exact prime_fortyThreeAO_877
      · exact prime_fortyThreeAO_39119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 329209064005537) ^ 164604532002768 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (15 : ZMod 329209064005537) ^ 109736354668512 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (15 : ZMod 329209064005537) ^ 29928096727776 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (15 : ZMod 329209064005537) ^ 25323774154272 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (15 : ZMod 329209064005537) ^ 1412914437792 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (15 : ZMod 329209064005537) ^ 375380916768 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (15 : ZMod 329209064005537) ^ 8415579744 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_391232175743963 : Nat.Prime 391232175743963 := by
  apply lucas_primality 391232175743963 (2 : ZMod 391232175743963)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (71, 1), (83, 1), (6091, 1), (778541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (71, 1), (83, 1), (6091, 1), (778541, 1)] : List FactorBlock).map factorBlockValue).prod) = 391232175743963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_71
      · exact prime_fortyThreeAO_83
      · exact prime_fortyThreeAO_6091
      · exact prime_fortyThreeAO_778541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 391232175743963) ^ 195616087871981 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 391232175743963) ^ 55890310820566 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 391232175743963) ^ 5510312334422 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 391232175743963) ^ 4713640671614 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 391232175743963) ^ 64231189582 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 391232175743963) ^ 502519682 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_752958657021607 : Nat.Prime 752958657021607 := by
  apply lucas_primality 752958657021607 (3 : ZMod 752958657021607)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13799, 1), (1299194657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13799, 1), (1299194657, 1)] : List FactorBlock).map factorBlockValue).prod) = 752958657021607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_13799
      · exact prime_fortyThreeAO_1299194657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 752958657021607) ^ 376479328510803 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 752958657021607) ^ 250986219007202 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 752958657021607) ^ 107565522431658 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 752958657021607) ^ 54566175594 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 752958657021607) ^ 579558 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_754921482177661 : Nat.Prime 754921482177661 := by
  apply lucas_primality 754921482177661 (6 : ZMod 754921482177661)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (4057, 1), (443044639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (4057, 1), (443044639, 1)] : List FactorBlock).map factorBlockValue).prod) = 754921482177661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_4057
      · exact prime_fortyThreeAO_443044639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 754921482177661) ^ 377460741088830 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 754921482177661) ^ 251640494059220 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 754921482177661) ^ 150984296435532 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 754921482177661) ^ 107845926025380 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 754921482177661) ^ 186078748380 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 754921482177661) ^ 1703940 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_774615155626387 : Nat.Prime 774615155626387 := by
  apply lucas_primality 774615155626387 (2 : ZMod 774615155626387)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (43034175312577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (43034175312577, 1)] : List FactorBlock).map factorBlockValue).prod) = 774615155626387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_43034175312577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 774615155626387) ^ 387307577813193 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 774615155626387) ^ 258205051875462 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 774615155626387) ^ 18 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_816703869304201 : Nat.Prime 816703869304201 := by
  apply lucas_primality 816703869304201 (13 : ZMod 816703869304201)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (29, 1), (97, 1), (483886639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (29, 1), (97, 1), (483886639, 1)] : List FactorBlock).map factorBlockValue).prod) = 816703869304201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_97
      · exact prime_fortyThreeAO_483886639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 816703869304201) ^ 408351934652100 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 816703869304201) ^ 272234623101400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 816703869304201) ^ 163340773860840 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 816703869304201) ^ 28162202389800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 816703869304201) ^ 8419627518600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 816703869304201) ^ 1687800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_901457477071441 : Nat.Prime 901457477071441 := by
  apply lucas_primality 901457477071441 (14 : ZMod 901457477071441)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (3499, 1), (1073470369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (3499, 1), (1073470369, 1)] : List FactorBlock).map factorBlockValue).prod) = 901457477071441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_3499
      · exact prime_fortyThreeAO_1073470369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 901457477071441) ^ 450728738535720 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 901457477071441) ^ 300485825690480 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 901457477071441) ^ 180291495414288 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 901457477071441) ^ 257632888560 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 901457477071441) ^ 839760 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1116138301851721 : Nat.Prime 1116138301851721 := by
  apply lucas_primality 1116138301851721 (17 : ZMod 1116138301851721)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (625861, 1), (2123053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (625861, 1), (2123053, 1)] : List FactorBlock).map factorBlockValue).prod) = 1116138301851721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_625861
      · exact prime_fortyThreeAO_2123053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1116138301851721) ^ 558069150925860 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (17 : ZMod 1116138301851721) ^ 372046100617240 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (17 : ZMod 1116138301851721) ^ 223227660370344 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (17 : ZMod 1116138301851721) ^ 159448328835960 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (17 : ZMod 1116138301851721) ^ 1783364520 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (17 : ZMod 1116138301851721) ^ 525723240 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1147656004877407 : Nat.Prime 1147656004877407 := by
  apply lucas_primality 1147656004877407 (3 : ZMod 1147656004877407)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (968027, 1), (197593663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (968027, 1), (197593663, 1)] : List FactorBlock).map factorBlockValue).prod) = 1147656004877407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_968027
      · exact prime_fortyThreeAO_197593663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1147656004877407) ^ 573828002438703 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1147656004877407) ^ 382552001625802 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1147656004877407) ^ 1185561978 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1147656004877407) ^ 5808162 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1152405966627703 : Nat.Prime 1152405966627703 := by
  apply lucas_primality 1152405966627703 (7 : ZMod 1152405966627703)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3779, 1), (73009, 1), (232049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3779, 1), (73009, 1), (232049, 1)] : List FactorBlock).map factorBlockValue).prod) = 1152405966627703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_3779
      · exact prime_fortyThreeAO_73009
      · exact prime_fortyThreeAO_232049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1152405966627703) ^ 576202983313851 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1152405966627703) ^ 384135322209234 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1152405966627703) ^ 304949977938 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1152405966627703) ^ 15784437078 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1152405966627703) ^ 4966218198 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1347287434223959 : Nat.Prime 1347287434223959 := by
  apply lucas_primality 1347287434223959 (3 : ZMod 1347287434223959)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (2063, 1), (2134222061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (2063, 1), (2134222061, 1)] : List FactorBlock).map factorBlockValue).prod) = 1347287434223959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_2063
      · exact prime_fortyThreeAO_2134222061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1347287434223959) ^ 673643717111979 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1347287434223959) ^ 449095811407986 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1347287434223959) ^ 79252202013174 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1347287434223959) ^ 653071950666 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1347287434223959) ^ 631278 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1662549515576219 : Nat.Prime 1662549515576219 := by
  apply lucas_primality 1662549515576219 (2 : ZMod 1662549515576219)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (6067698961957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (6067698961957, 1)] : List FactorBlock).map factorBlockValue).prod) = 1662549515576219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_137
      · exact prime_fortyThreeAO_6067698961957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1662549515576219) ^ 831274757788109 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1662549515576219) ^ 12135397923914 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1662549515576219) ^ 274 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_41
      · exact prime_fortyThreeAO_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_2254175965482383 : Nat.Prime 2254175965482383 := by
  apply lucas_primality 2254175965482383 (5 : ZMod 2254175965482383)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (2539, 1), (81527, 1), (320291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (2539, 1), (81527, 1), (320291, 1)] : List FactorBlock).map factorBlockValue).prod) = 2254175965482383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_2539
      · exact prime_fortyThreeAO_81527
      · exact prime_fortyThreeAO_320291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2254175965482383) ^ 1127087982741191 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2254175965482383) ^ 132598586204846 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2254175965482383) ^ 887820388138 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2254175965482383) ^ 27649440866 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2254175965482383) ^ 7037899802 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_3801426658851893 : Nat.Prime 3801426658851893 := by
  apply lucas_primality 3801426658851893 (2 : ZMod 3801426658851893)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (135765237816139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (135765237816139, 1)] : List FactorBlock).map factorBlockValue).prod) = 3801426658851893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_135765237816139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3801426658851893) ^ 1900713329425946 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3801426658851893) ^ 543060951264556 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3801426658851893) ^ 28 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_4801158693898529 : Nat.Prime 4801158693898529 := by
  apply lucas_primality 4801158693898529 (3 : ZMod 4801158693898529)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (22433, 1), (514476301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (22433, 1), (514476301, 1)] : List FactorBlock).map factorBlockValue).prod) = 4801158693898529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_22433
      · exact prime_fortyThreeAO_514476301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4801158693898529) ^ 2400579346949264 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4801158693898529) ^ 369319899530656 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4801158693898529) ^ 214022141216 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4801158693898529) ^ 9332128 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_5158728367066649 : Nat.Prime 5158728367066649 := by
  apply lucas_primality 5158728367066649 (3 : ZMod 5158728367066649)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 4), (5647, 1), (7799453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 4), (5647, 1), (7799453, 1)] : List FactorBlock).map factorBlockValue).prod) = 5158728367066649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_5647
      · exact prime_fortyThreeAO_7799453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5158728367066649) ^ 2579364183533324 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5158728367066649) ^ 468975306096968 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5158728367066649) ^ 913534330984 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5158728367066649) ^ 661421816 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_6418665295315729 : Nat.Prime 6418665295315729 := by
  apply lucas_primality 6418665295315729 (19 : ZMod 6418665295315729)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (13, 1), (1469474655521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (13, 1), (1469474655521, 1)] : List FactorBlock).map factorBlockValue).prod) = 6418665295315729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_1469474655521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 6418665295315729) ^ 3209332647657864 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (19 : ZMod 6418665295315729) ^ 2139555098438576 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (19 : ZMod 6418665295315729) ^ 916952185045104 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (19 : ZMod 6418665295315729) ^ 493743484255056 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (19 : ZMod 6418665295315729) ^ 4368 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_6885936029264443 : Nat.Prime 6885936029264443 := by
  apply lucas_primality 6885936029264443 (2 : ZMod 6885936029264443)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1147656004877407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1147656004877407, 1)] : List FactorBlock).map factorBlockValue).prod) = 6885936029264443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_1147656004877407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6885936029264443) ^ 3442968014632221 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6885936029264443) ^ 2295312009754814 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6885936029264443) ^ 6 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_7557523650251027 : Nat.Prime 7557523650251027 := by
  apply lucas_primality 7557523650251027 (2 : ZMod 7557523650251027)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (50321, 1), (54949, 1), (1366597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (50321, 1), (54949, 1), (1366597, 1)] : List FactorBlock).map factorBlockValue).prod) = 7557523650251027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_50321
      · exact prime_fortyThreeAO_54949
      · exact prime_fortyThreeAO_1366597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7557523650251027) ^ 3778761825125513 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7557523650251027) ^ 150186277106 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7557523650251027) ^ 137537055274 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7557523650251027) ^ 5530177258 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_7571667148839749 : Nat.Prime 7571667148839749 := by
  apply lucas_primality 7571667148839749 (2 : ZMod 7571667148839749)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2267, 1), (834987555011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2267, 1), (834987555011, 1)] : List FactorBlock).map factorBlockValue).prod) = 7571667148839749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_2267
      · exact prime_fortyThreeAO_834987555011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7571667148839749) ^ 3785833574419874 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7571667148839749) ^ 3339950220044 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7571667148839749) ^ 9068 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_10330891742740993 : Nat.Prime 10330891742740993 := by
  apply lucas_primality 10330891742740993 (5 : ZMod 10330891742740993)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (6725840978347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (6725840978347, 1)] : List FactorBlock).map factorBlockValue).prod) = 10330891742740993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_6725840978347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 10330891742740993) ^ 5165445871370496 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 10330891742740993) ^ 3443630580913664 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 10330891742740993) ^ 1536 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_12735793724305513 : Nat.Prime 12735793724305513 := by
  apply lucas_primality 12735793724305513 (10 : ZMod 12735793724305513)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (10829756568287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (10829756568287, 1)] : List FactorBlock).map factorBlockValue).prod) = 12735793724305513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_10829756568287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 12735793724305513) ^ 6367896862152756 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 12735793724305513) ^ 4245264574768504 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 12735793724305513) ^ 1819399103472216 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 12735793724305513) ^ 1176 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_14844601172534317 : Nat.Prime 14844601172534317 := by
  apply lucas_primality 14844601172534317 (5 : ZMod 14844601172534317)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (269, 1), (571, 1), (5273, 1), (32497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (269, 1), (571, 1), (5273, 1), (32497, 1)] : List FactorBlock).map factorBlockValue).prod) = 14844601172534317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_47
      · exact prime_fortyThreeAO_269
      · exact prime_fortyThreeAO_571
      · exact prime_fortyThreeAO_5273
      · exact prime_fortyThreeAO_32497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 14844601172534317) ^ 7422300586267158 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14844601172534317) ^ 4948200390844772 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14844601172534317) ^ 315842578139028 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14844601172534317) ^ 55184390975964 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14844601172534317) ^ 25997550214596 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14844601172534317) ^ 2815209780492 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14844601172534317) ^ 456799125228 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_24930148441763503 : Nat.Prime 24930148441763503 := by
  apply lucas_primality 24930148441763503 (5 : ZMod 24930148441763503)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (41, 1), (709, 1), (756278437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (41, 1), (709, 1), (756278437, 1)] : List FactorBlock).map factorBlockValue).prod) = 24930148441763503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_41
      · exact prime_fortyThreeAO_709
      · exact prime_fortyThreeAO_756278437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 24930148441763503) ^ 12465074220881751 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 24930148441763503) ^ 8310049480587834 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 24930148441763503) ^ 3561449777394786 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 24930148441763503) ^ 608052401018622 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 24930148441763503) ^ 35162409649878 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 24930148441763503) ^ 32964246 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_34742177880057719 : Nat.Prime 34742177880057719 := by
  apply lucas_primality 34742177880057719 (7 : ZMod 34742177880057719)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (197, 1), (1282951, 1), (9818671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (197, 1), (1282951, 1), (9818671, 1)] : List FactorBlock).map factorBlockValue).prod) = 34742177880057719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_197
      · exact prime_fortyThreeAO_1282951
      · exact prime_fortyThreeAO_9818671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 34742177880057719) ^ 17371088940028859 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 34742177880057719) ^ 4963168268579674 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 34742177880057719) ^ 176356232893694 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 34742177880057719) ^ 27079894618 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 34742177880057719) ^ 3538378858 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_49761680828486743 : Nat.Prime 49761680828486743 := by
  apply lucas_primality 49761680828486743 (6 : ZMod 49761680828486743)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (131, 1), (218623, 1), (96528463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (131, 1), (218623, 1), (96528463, 1)] : List FactorBlock).map factorBlockValue).prod) = 49761680828486743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_131
      · exact prime_fortyThreeAO_218623
      · exact prime_fortyThreeAO_96528463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 49761680828486743) ^ 24880840414243371 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 49761680828486743) ^ 16587226942828914 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 49761680828486743) ^ 379860158996082 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 49761680828486743) ^ 227614115754 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 49761680828486743) ^ 515513034 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_80016656703522589 : Nat.Prime 80016656703522589 := by
  apply lucas_primality 80016656703522589 (6 : ZMod 80016656703522589)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (7, 1), (769, 1), (15292896763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (7, 1), (769, 1), (15292896763, 1)] : List FactorBlock).map factorBlockValue).prod) = 80016656703522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_769
      · exact prime_fortyThreeAO_15292896763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 80016656703522589) ^ 40008328351761294 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 80016656703522589) ^ 26672218901174196 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 80016656703522589) ^ 11430950957646084 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 80016656703522589) ^ 104052869575452 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 80016656703522589) ^ 5232276 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_83127475778810951 : Nat.Prime 83127475778810951 := by
  apply lucas_primality 83127475778810951 (11 : ZMod 83127475778810951)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1662549515576219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1662549515576219, 1)] : List FactorBlock).map factorBlockValue).prod) = 83127475778810951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_1662549515576219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 83127475778810951) ^ 41563737889405475 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 83127475778810951) ^ 16625495155762190 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (11 : ZMod 83127475778810951) ^ 50 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_104199761661508873 : Nat.Prime 104199761661508873 := by
  apply lucas_primality 104199761661508873 (5 : ZMod 104199761661508873)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 6), (191, 1), (877, 1), (3889, 1), (27427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 6), (191, 1), (877, 1), (3889, 1), (27427, 1)] : List FactorBlock).map factorBlockValue).prod) = 104199761661508873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_191
      · exact prime_fortyThreeAO_877
      · exact prime_fortyThreeAO_3889
      · exact prime_fortyThreeAO_27427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 104199761661508873) ^ 52099880830754436 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 104199761661508873) ^ 34733253887169624 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 104199761661508873) ^ 545548490374392 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 104199761661508873) ^ 118813867344936 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 104199761661508873) ^ 26793458899848 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 104199761661508873) ^ 3799167304536 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_221061418313708267 : Nat.Prime 221061418313708267 := by
  apply lucas_primality 221061418313708267 (2 : ZMod 221061418313708267)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (61, 1), (457, 1), (3539, 1), (5003, 1), (31991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (61, 1), (457, 1), (3539, 1), (5003, 1), (31991, 1)] : List FactorBlock).map factorBlockValue).prod) = 221061418313708267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_61
      · exact prime_fortyThreeAO_457
      · exact prime_fortyThreeAO_3539
      · exact prime_fortyThreeAO_5003
      · exact prime_fortyThreeAO_31991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 221061418313708267) ^ 110530709156854133 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 221061418313708267) ^ 31580202616244038 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 221061418313708267) ^ 3623957677273906 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 221061418313708267) ^ 483723016003738 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 221061418313708267) ^ 62464373640494 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 221061418313708267) ^ 44185772199422 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 221061418313708267) ^ 6910112791526 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_237513618760549073 : Nat.Prime 237513618760549073 := by
  apply lucas_primality 237513618760549073 (3 : ZMod 237513618760549073)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (14844601172534317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (14844601172534317, 1)] : List FactorBlock).map factorBlockValue).prod) = 237513618760549073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_14844601172534317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 237513618760549073) ^ 118756809380274536 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 237513618760549073) ^ 16 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_287726304385453069 : Nat.Prime 287726304385453069 := by
  apply lucas_primality 287726304385453069 (2 : ZMod 287726304385453069)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (3607, 1), (392069, 1), (5651561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (3607, 1), (392069, 1), (5651561, 1)] : List FactorBlock).map factorBlockValue).prod) = 287726304385453069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_3607
      · exact prime_fortyThreeAO_392069
      · exact prime_fortyThreeAO_5651561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 287726304385453069) ^ 143863152192726534 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 287726304385453069) ^ 95908768128484356 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 287726304385453069) ^ 79768867309524 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 287726304385453069) ^ 733866498972 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 287726304385453069) ^ 50910943788 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_299161781301162037 : Nat.Prime 299161781301162037 := by
  apply lucas_primality 299161781301162037 (5 : ZMod 299161781301162037)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (24930148441763503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (24930148441763503, 1)] : List FactorBlock).map factorBlockValue).prod) = 299161781301162037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_24930148441763503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 299161781301162037) ^ 149580890650581018 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 299161781301162037) ^ 99720593767054012 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 299161781301162037) ^ 12 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_363440023144307953 : Nat.Prime 363440023144307953 := by
  apply lucas_primality 363440023144307953 (10 : ZMod 363440023144307953)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7571667148839749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7571667148839749, 1)] : List FactorBlock).map factorBlockValue).prod) = 363440023144307953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7571667148839749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 363440023144307953) ^ 181720011572153976 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 363440023144307953) ^ 121146674381435984 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 363440023144307953) ^ 48 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_454244353583729437 : Nat.Prime 454244353583729437 := by
  apply lucas_primality 454244353583729437 (2 : ZMod 454244353583729437)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (13, 2), (1931, 1), (5523571987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (13, 2), (1931, 1), (5523571987, 1)] : List FactorBlock).map factorBlockValue).prod) = 454244353583729437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_1931
      · exact prime_fortyThreeAO_5523571987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 454244353583729437) ^ 227122176791864718 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 454244353583729437) ^ 151414784527909812 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 454244353583729437) ^ 64892050511961348 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 454244353583729437) ^ 34941873352594572 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 454244353583729437) ^ 235237883782356 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 454244353583729437) ^ 82237428 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_61717
      · exact prime_fortyThreeAO_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_601679865410253247 : Nat.Prime 601679865410253247 := by
  apply lucas_primality 601679865410253247 (5 : ZMod 601679865410253247)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (1657, 1), (587563074971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (1657, 1), (587563074971, 1)] : List FactorBlock).map factorBlockValue).prod) = 601679865410253247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_103
      · exact prime_fortyThreeAO_1657
      · exact prime_fortyThreeAO_587563074971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 601679865410253247) ^ 300839932705126623 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 601679865410253247) ^ 200559955136751082 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 601679865410253247) ^ 5841552091361682 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 601679865410253247) ^ 363113980332078 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 601679865410253247) ^ 1024026 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_928803381995832767 : Nat.Prime 928803381995832767 := by
  apply lucas_primality 928803381995832767 (5 : ZMod 928803381995832767)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (197, 1), (138668764108067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (197, 1), (138668764108067, 1)] : List FactorBlock).map factorBlockValue).prod) = 928803381995832767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_197
      · exact prime_fortyThreeAO_138668764108067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 928803381995832767) ^ 464401690997916383 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 928803381995832767) ^ 54635493058578398 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 928803381995832767) ^ 4714737979674278 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 928803381995832767) ^ 6698 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_970258947223505683 : Nat.Prime 970258947223505683 := by
  apply lucas_primality 970258947223505683 (5 : ZMod 970258947223505683)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (163, 1), (193, 1), (123407, 1), (2450207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (163, 1), (193, 1), (123407, 1), (2450207, 1)] : List FactorBlock).map factorBlockValue).prod) = 970258947223505683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_163
      · exact prime_fortyThreeAO_193
      · exact prime_fortyThreeAO_123407
      · exact prime_fortyThreeAO_2450207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 970258947223505683) ^ 485129473611752841 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 970258947223505683) ^ 323419649074501894 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 970258947223505683) ^ 57074055719029746 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 970258947223505683) ^ 5952508878671814 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 970258947223505683) ^ 5027248431209874 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 970258947223505683) ^ 7862268325326 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 970258947223505683) ^ 395990602926 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1410241656255369677 : Nat.Prime 1410241656255369677 := by
  apply lucas_primality 1410241656255369677 (2 : ZMod 1410241656255369677)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7603, 1), (8623, 1), (57667, 1), (93253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7603, 1), (8623, 1), (57667, 1), (93253, 1)] : List FactorBlock).map factorBlockValue).prod) = 1410241656255369677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7603
      · exact prime_fortyThreeAO_8623
      · exact prime_fortyThreeAO_57667
      · exact prime_fortyThreeAO_93253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1410241656255369677) ^ 705120828127684838 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1410241656255369677) ^ 185484894943492 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1410241656255369677) ^ 163544202279412 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1410241656255369677) ^ 24454916265028 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1410241656255369677) ^ 15122748396892 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_8461449937532218063 : Nat.Prime 8461449937532218063 := by
  apply lucas_primality 8461449937532218063 (3 : ZMod 8461449937532218063)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1410241656255369677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1410241656255369677, 1)] : List FactorBlock).map factorBlockValue).prod) = 8461449937532218063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_1410241656255369677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8461449937532218063) ^ 4230724968766109031 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 8461449937532218063) ^ 2820483312510739354 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 8461449937532218063) ^ 6 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_9255672634098534199 : Nat.Prime 9255672634098534199 := by
  apply lucas_primality 9255672634098534199 (3 : ZMod 9255672634098534199)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (49761680828486743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (49761680828486743, 1)] : List FactorBlock).map factorBlockValue).prod) = 9255672634098534199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_31
      · exact prime_fortyThreeAO_49761680828486743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9255672634098534199) ^ 4627836317049267099 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 9255672634098534199) ^ 3085224211366178066 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 9255672634098534199) ^ 298570084970920458 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 9255672634098534199) ^ 186 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_13115360895995606113 : Nat.Prime 13115360895995606113 := by
  apply lucas_primality 13115360895995606113 (5 : ZMod 13115360895995606113)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (719, 1), (63337201050821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (719, 1), (63337201050821, 1)] : List FactorBlock).map factorBlockValue).prod) = 13115360895995606113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_719
      · exact prime_fortyThreeAO_63337201050821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 13115360895995606113) ^ 6557680447997803056 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 13115360895995606113) ^ 4371786965331868704 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 13115360895995606113) ^ 18241113902636448 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 13115360895995606113) ^ 207072 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_20976733589071979441 : Nat.Prime 20976733589071979441 := by
  apply lucas_primality 20976733589071979441 (3 : ZMod 20976733589071979441)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (113, 1), (283, 1), (5569, 1), (9059, 1), (162527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (113, 1), (283, 1), (5569, 1), (9059, 1), (162527, 1)] : List FactorBlock).map factorBlockValue).prod) = 20976733589071979441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_113
      · exact prime_fortyThreeAO_283
      · exact prime_fortyThreeAO_5569
      · exact prime_fortyThreeAO_9059
      · exact prime_fortyThreeAO_162527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20976733589071979441) ^ 10488366794535989720 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 20976733589071979441) ^ 4195346717814395888 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 20976733589071979441) ^ 185634810522760880 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 20976733589071979441) ^ 74122733530289680 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 20976733589071979441) ^ 3766696640163760 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 20976733589071979441) ^ 2315568339670160 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 20976733589071979441) ^ 129066146480720 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_22023996649499173583 : Nat.Prime 22023996649499173583 := by
  apply lucas_primality 22023996649499173583 (5 : ZMod 22023996649499173583)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (691, 1), (72823, 1), (19894216417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (691, 1), (72823, 1), (19894216417, 1)] : List FactorBlock).map factorBlockValue).prod) = 22023996649499173583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_691
      · exact prime_fortyThreeAO_72823
      · exact prime_fortyThreeAO_19894216417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 22023996649499173583) ^ 11011998324749586791 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 22023996649499173583) ^ 2002181513590833962 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 22023996649499173583) ^ 31872643486974202 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 22023996649499173583) ^ 302431877971234 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 22023996649499173583) ^ 1107055246 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_24169009568378057797 : Nat.Prime 24169009568378057797 := by
  apply lucas_primality 24169009568378057797 (6 : ZMod 24169009568378057797)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (287726304385453069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (287726304385453069, 1)] : List FactorBlock).map factorBlockValue).prod) = 24169009568378057797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_287726304385453069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 24169009568378057797) ^ 12084504784189028898 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 24169009568378057797) ^ 8056336522792685932 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 24169009568378057797) ^ 3452715652625436828 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 24169009568378057797) ^ 84 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_26056334574040524623 : Nat.Prime 26056334574040524623 := by
  apply lucas_primality 26056334574040524623 (5 : ZMod 26056334574040524623)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (12541, 1), (94440542562361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (12541, 1), (94440542562361, 1)] : List FactorBlock).map factorBlockValue).prod) = 26056334574040524623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_12541
      · exact prime_fortyThreeAO_94440542562361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 26056334574040524623) ^ 13028167287020262311 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 26056334574040524623) ^ 2368757688549138602 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 26056334574040524623) ^ 2077691936371942 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 26056334574040524623) ^ 275902 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_49920724444456147039 : Nat.Prime 49920724444456147039 := by
  apply lucas_primality 49920724444456147039 (3 : ZMod 49920724444456147039)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (2749, 1), (27766963602253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (2749, 1), (27766963602253, 1)] : List FactorBlock).map factorBlockValue).prod) = 49920724444456147039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_109
      · exact prime_fortyThreeAO_2749
      · exact prime_fortyThreeAO_27766963602253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 49920724444456147039) ^ 24960362222228073519 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 49920724444456147039) ^ 16640241481485382346 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 49920724444456147039) ^ 457988297655560982 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 49920724444456147039) ^ 18159594195873462 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 49920724444456147039) ^ 1797846 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_60694026617241508171 : Nat.Prime 60694026617241508171 := by
  apply lucas_primality 60694026617241508171 (2 : ZMod 60694026617241508171)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (5711, 1), (671123, 1), (527849863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (5711, 1), (671123, 1), (527849863, 1)] : List FactorBlock).map factorBlockValue).prod) = 60694026617241508171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_5711
      · exact prime_fortyThreeAO_671123
      · exact prime_fortyThreeAO_527849863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60694026617241508171) ^ 30347013308620754085 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 60694026617241508171) ^ 20231342205747169390 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 60694026617241508171) ^ 12138805323448301634 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 60694026617241508171) ^ 10627565508184470 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 60694026617241508171) ^ 90436517027790 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 60694026617241508171) ^ 114983503590 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_96676038273512231189 : Nat.Prime 96676038273512231189 := by
  apply lucas_primality 96676038273512231189 (2 : ZMod 96676038273512231189)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (24169009568378057797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (24169009568378057797, 1)] : List FactorBlock).map factorBlockValue).prod) = 96676038273512231189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_24169009568378057797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 96676038273512231189) ^ 48338019136756115594 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 96676038273512231189) ^ 4 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_107517294063490759649 : Nat.Prime 107517294063490759649 := by
  apply lucas_primality 107517294063490759649 (3 : ZMod 107517294063490759649)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (103, 1), (9391, 1), (3473595809543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (103, 1), (9391, 1), (3473595809543, 1)] : List FactorBlock).map factorBlockValue).prod) = 107517294063490759649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_103
      · exact prime_fortyThreeAO_9391
      · exact prime_fortyThreeAO_3473595809543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 107517294063490759649) ^ 53758647031745379824 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 107517294063490759649) ^ 1043857223917386016 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 107517294063490759649) ^ 11448971788253728 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 107517294063490759649) ^ 30952736 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_107563409109560591969 : Nat.Prime 107563409109560591969 := by
  apply lucas_primality 107563409109560591969 (3 : ZMod 107563409109560591969)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (18670303, 1), (16367054503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (18670303, 1), (16367054503, 1)] : List FactorBlock).map factorBlockValue).prod) = 107563409109560591969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_18670303
      · exact prime_fortyThreeAO_16367054503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 107563409109560591969) ^ 53781704554780295984 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 107563409109560591969) ^ 9778491737232781088 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 107563409109560591969) ^ 5761203185056 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 107563409109560591969) ^ 6571946656 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_138078489775522654669 : Nat.Prime 138078489775522654669 := by
  apply lucas_primality 138078489775522654669 (6 : ZMod 138078489775522654669)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (73, 1), (193, 1), (816703869304201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (73, 1), (193, 1), (816703869304201, 1)] : List FactorBlock).map factorBlockValue).prod) = 138078489775522654669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_73
      · exact prime_fortyThreeAO_193
      · exact prime_fortyThreeAO_816703869304201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 138078489775522654669) ^ 69039244887761327334 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 138078489775522654669) ^ 46026163258507551556 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 138078489775522654669) ^ 1891486161308529516 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 138078489775522654669) ^ 715432589510480076 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 138078489775522654669) ^ 169068 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_158992423920783882271 : Nat.Prime 158992423920783882271 := by
  apply lucas_primality 158992423920783882271 (3 : ZMod 158992423920783882271)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (19, 1), (10330891742740993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (19, 1), (10330891742740993, 1)] : List FactorBlock).map factorBlockValue).prod) = 158992423920783882271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_10330891742740993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 158992423920783882271) ^ 79496211960391941135 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 158992423920783882271) ^ 52997474640261294090 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 158992423920783882271) ^ 31798484784156776454 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 158992423920783882271) ^ 8368022311620204330 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 158992423920783882271) ^ 15390 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_199682897777824588157 : Nat.Prime 199682897777824588157 := by
  apply lucas_primality 199682897777824588157 (2 : ZMod 199682897777824588157)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (49920724444456147039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (49920724444456147039, 1)] : List FactorBlock).map factorBlockValue).prod) = 199682897777824588157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_49920724444456147039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 199682897777824588157) ^ 99841448888912294078 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 199682897777824588157) ^ 4 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_316996091778026056271 : Nat.Prime 316996091778026056271 := by
  apply lucas_primality 316996091778026056271 (13 : ZMod 316996091778026056271)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (79, 1), (5227, 1), (10966707908617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (79, 1), (5227, 1), (10966707908617, 1)] : List FactorBlock).map factorBlockValue).prod) = 316996091778026056271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_79
      · exact prime_fortyThreeAO_5227
      · exact prime_fortyThreeAO_10966707908617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 316996091778026056271) ^ 158498045889013028135 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 316996091778026056271) ^ 63399218355605211254 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 316996091778026056271) ^ 45285155968289436610 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 316996091778026056271) ^ 4012608756683874130 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 316996091778026056271) ^ 60645894734652010 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (13 : ZMod 316996091778026056271) ^ 28905310 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_900131140186208514877 : Nat.Prime 900131140186208514877 := by
  apply lucas_primality 900131140186208514877 (2 : ZMod 900131140186208514877)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (26029, 1), (100057, 1), (152063, 1), (189407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (26029, 1), (100057, 1), (152063, 1), (189407, 1)] : List FactorBlock).map factorBlockValue).prod) = 900131140186208514877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_26029
      · exact prime_fortyThreeAO_100057
      · exact prime_fortyThreeAO_152063
      · exact prime_fortyThreeAO_189407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 900131140186208514877) ^ 450065570093104257438 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 900131140186208514877) ^ 300043713395402838292 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 900131140186208514877) ^ 34581856398102444 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 900131140186208514877) ^ 8996183577223068 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 900131140186208514877) ^ 5919461934765252 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 900131140186208514877) ^ 4752364697113668 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1109961537321118874573 : Nat.Prime 1109961537321118874573 := by
  apply lucas_primality 1109961537321118874573 (2 : ZMod 1109961537321118874573)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (33617, 1), (191964326140553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (33617, 1), (191964326140553, 1)] : List FactorBlock).map factorBlockValue).prod) = 1109961537321118874573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_43
      · exact prime_fortyThreeAO_33617
      · exact prime_fortyThreeAO_191964326140553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1109961537321118874573) ^ 554980768660559437286 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1109961537321118874573) ^ 25813059007467880804 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1109961537321118874573) ^ 33017864096175116 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1109961537321118874573) ^ 5782124 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1782829504095638945459 : Nat.Prime 1782829504095638945459 := by
  apply lucas_primality 1782829504095638945459 (2 : ZMod 1782829504095638945459)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (193, 1), (10531, 1), (25799065421539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (193, 1), (10531, 1), (25799065421539, 1)] : List FactorBlock).map factorBlockValue).prod) = 1782829504095638945459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_193
      · exact prime_fortyThreeAO_10531
      · exact prime_fortyThreeAO_25799065421539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1782829504095638945459) ^ 891414752047819472729 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1782829504095638945459) ^ 104872323770331702674 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1782829504095638945459) ^ 9237458570443725106 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1782829504095638945459) ^ 169293467296138918 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1782829504095638945459) ^ 69104422 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_107
      · exact prime_fortyThreeAO_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_2647346742384404952877 : Nat.Prime 2647346742384404952877 := by
  apply lucas_primality 2647346742384404952877 (2 : ZMod 2647346742384404952877)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (193, 1), (727, 1), (21996109, 1), (71481227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (193, 1), (727, 1), (21996109, 1), (71481227, 1)] : List FactorBlock).map factorBlockValue).prod) = 2647346742384404952877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_193
      · exact prime_fortyThreeAO_727
      · exact prime_fortyThreeAO_21996109
      · exact prime_fortyThreeAO_71481227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2647346742384404952877) ^ 1323673371192202476438 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2647346742384404952877) ^ 882448914128134984292 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2647346742384404952877) ^ 13716822499401061932 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2647346742384404952877) ^ 3641467321023940788 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2647346742384404952877) ^ 120355229299164 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2647346742384404952877) ^ 37035552598788 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_4060393607487513709939 : Nat.Prime 4060393607487513709939 := by
  apply lucas_primality 4060393607487513709939 (3 : ZMod 4060393607487513709939)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (96676038273512231189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (96676038273512231189, 1)] : List FactorBlock).map factorBlockValue).prod) = 4060393607487513709939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_96676038273512231189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4060393607487513709939) ^ 2030196803743756854969 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4060393607487513709939) ^ 1353464535829171236646 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4060393607487513709939) ^ 580056229641073387134 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4060393607487513709939) ^ 42 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_4633494704020955437129 : Nat.Prime 4633494704020955437129 := by
  apply lucas_primality 4633494704020955437129 (7 : ZMod 4633494704020955437129)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (71, 1), (367, 1), (15131, 1), (179533, 1), (303053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (71, 1), (367, 1), (15131, 1), (179533, 1), (303053, 1)] : List FactorBlock).map factorBlockValue).prod) = 4633494704020955437129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_71
      · exact prime_fortyThreeAO_367
      · exact prime_fortyThreeAO_15131
      · exact prime_fortyThreeAO_179533
      · exact prime_fortyThreeAO_303053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4633494704020955437129) ^ 2316747352010477718564 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 4633494704020955437129) ^ 1544498234673651812376 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 4633494704020955437129) ^ 65260488789027541368 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 4633494704020955437129) ^ 12625326168994428984 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 4633494704020955437129) ^ 306225279493817688 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 4633494704020955437129) ^ 25808596213626216 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 4633494704020955437129) ^ 15289387348156776 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_6210767055158766950407 : Nat.Prime 6210767055158766950407 := by
  apply lucas_primality 6210767055158766950407 (5 : ZMod 6210767055158766950407)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (22023996649499173583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (22023996649499173583, 1)] : List FactorBlock).map factorBlockValue).prod) = 6210767055158766950407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_47
      · exact prime_fortyThreeAO_22023996649499173583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6210767055158766950407) ^ 3105383527579383475203 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6210767055158766950407) ^ 2070255685052922316802 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6210767055158766950407) ^ 132143979896995041498 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6210767055158766950407) ^ 282 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_7689470924282987411419 : Nat.Prime 7689470924282987411419 := by
  apply lucas_primality 7689470924282987411419 (2 : ZMod 7689470924282987411419)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (53, 1), (6271, 1), (50077404703553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (53, 1), (6271, 1), (50077404703553, 1)] : List FactorBlock).map factorBlockValue).prod) = 7689470924282987411419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_53
      · exact prime_fortyThreeAO_6271
      · exact prime_fortyThreeAO_50077404703553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7689470924282987411419) ^ 3844735462141493705709 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7689470924282987411419) ^ 2563156974760995803806 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7689470924282987411419) ^ 1098495846326141058774 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7689470924282987411419) ^ 699042811298453401038 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7689470924282987411419) ^ 145084357061943158706 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7689470924282987411419) ^ 1226195331571198758 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7689470924282987411419) ^ 153551706 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_12020361862165985109283 : Nat.Prime 12020361862165985109283 := by
  apply lucas_primality 12020361862165985109283 (5 : ZMod 12020361862165985109283)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (83, 1), (2873621, 1), (365200088723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (83, 1), (2873621, 1), (365200088723, 1)] : List FactorBlock).map factorBlockValue).prod) = 12020361862165985109283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_83
      · exact prime_fortyThreeAO_2873621
      · exact prime_fortyThreeAO_365200088723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12020361862165985109283) ^ 6010180931082992554641 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 12020361862165985109283) ^ 4006787287388661703094 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 12020361862165985109283) ^ 522624428789825439534 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 12020361862165985109283) ^ 144823636893566085654 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 12020361862165985109283) ^ 4183001816233242 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 12020361862165985109283) ^ 32914454934 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_14079907167821039345653 : Nat.Prime 14079907167821039345653 := by
  apply lucas_primality 14079907167821039345653 (5 : ZMod 14079907167821039345653)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (19, 1), (1069, 1), (6418665295315729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (19, 1), (1069, 1), (6418665295315729, 1)] : List FactorBlock).map factorBlockValue).prod) = 14079907167821039345653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_1069
      · exact prime_fortyThreeAO_6418665295315729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 14079907167821039345653) ^ 7039953583910519672826 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14079907167821039345653) ^ 4693302389273679781884 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14079907167821039345653) ^ 741047745674791544508 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14079907167821039345653) ^ 13171101185987875908 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14079907167821039345653) ^ 2193588 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_14543837805963257392933 : Nat.Prime 14543837805963257392933 := by
  apply lucas_primality 14543837805963257392933 (2 : ZMod 14543837805963257392933)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (71, 1), (1103, 1), (5158728367066649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (71, 1), (1103, 1), (5158728367066649, 1)] : List FactorBlock).map factorBlockValue).prod) = 14543837805963257392933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_71
      · exact prime_fortyThreeAO_1103
      · exact prime_fortyThreeAO_5158728367066649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14543837805963257392933) ^ 7271918902981628696466 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 14543837805963257392933) ^ 4847945935321085797644 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 14543837805963257392933) ^ 204842785999482498492 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 14543837805963257392933) ^ 13185709706222354844 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 14543837805963257392933) ^ 2819268 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_14634538943486215100689 : Nat.Prime 14634538943486215100689 := by
  apply lucas_primality 14634538943486215100689 (14 : ZMod 14634538943486215100689)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (11, 1), (17, 2), (43, 1), (349, 1), (236695299101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (11, 1), (17, 2), (43, 1), (349, 1), (236695299101, 1)] : List FactorBlock).map factorBlockValue).prod) = 14634538943486215100689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_43
      · exact prime_fortyThreeAO_349
      · exact prime_fortyThreeAO_236695299101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 14634538943486215100689) ^ 7317269471743107550344 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 14634538943486215100689) ^ 4878179647828738366896 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 14634538943486215100689) ^ 1330412631226019554608 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 14634538943486215100689) ^ 860855231969777358864 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 14634538943486215100689) ^ 340338114964795700016 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 14634538943486215100689) ^ 41932776342367378512 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 14634538943486215100689) ^ 61828599888 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_14886278882812275260783 : Nat.Prime 14886278882812275260783 := by
  apply lucas_primality 14886278882812275260783 (5 : ZMod 14886278882812275260783)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (312986969, 1), (23780988279439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (312986969, 1), (23780988279439, 1)] : List FactorBlock).map factorBlockValue).prod) = 14886278882812275260783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_312986969
      · exact prime_fortyThreeAO_23780988279439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 14886278882812275260783) ^ 7443139441406137630391 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14886278882812275260783) ^ 47561976558878 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14886278882812275260783) ^ 625973938 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_42946633384826817384103 : Nat.Prime 42946633384826817384103 := by
  apply lucas_primality 42946633384826817384103 (3 : ZMod 42946633384826817384103)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (201049, 1), (391232175743963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (201049, 1), (391232175743963, 1)] : List FactorBlock).map factorBlockValue).prod) = 42946633384826817384103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_201049
      · exact prime_fortyThreeAO_391232175743963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 42946633384826817384103) ^ 21473316692413408692051 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42946633384826817384103) ^ 14315544461608939128034 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42946633384826817384103) ^ 6135233340689545340586 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42946633384826817384103) ^ 3303587183448216721854 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42946633384826817384103) ^ 213612767956203798 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42946633384826817384103) ^ 109772754 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_51594155906952726185221 : Nat.Prime 51594155906952726185221 := by
  apply lucas_primality 51594155906952726185221 (6 : ZMod 51594155906952726185221)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (17, 1), (23, 1), (97, 1), (7557523650251027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (17, 1), (23, 1), (97, 1), (7557523650251027, 1)] : List FactorBlock).map factorBlockValue).prod) = 51594155906952726185221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_97
      · exact prime_fortyThreeAO_7557523650251027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 51594155906952726185221) ^ 25797077953476363092610 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 51594155906952726185221) ^ 17198051968984242061740 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 51594155906952726185221) ^ 10318831181390545237044 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 51594155906952726185221) ^ 3034950347467807422660 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 51594155906952726185221) ^ 2243224169867509834140 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 51594155906952726185221) ^ 531898514504667280260 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (6 : ZMod 51594155906952726185221) ^ 6826860 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_89328659364725301618659 : Nat.Prime 89328659364725301618659 := by
  apply lucas_primality 89328659364725301618659 (2 : ZMod 89328659364725301618659)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (4060393607487513709939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (4060393607487513709939, 1)] : List FactorBlock).map factorBlockValue).prod) = 89328659364725301618659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_4060393607487513709939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 89328659364725301618659) ^ 44664329682362650809329 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 89328659364725301618659) ^ 8120787214975027419878 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 89328659364725301618659) ^ 22 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_209333492618698302284453 : Nat.Prime 209333492618698302284453 := by
  apply lucas_primality 209333492618698302284453 (2 : ZMod 209333492618698302284453)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (317, 1), (1467953, 1), (10223853786983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (317, 1), (1467953, 1), (10223853786983, 1)] : List FactorBlock).map factorBlockValue).prod) = 209333492618698302284453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_317
      · exact prime_fortyThreeAO_1467953
      · exact prime_fortyThreeAO_10223853786983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 209333492618698302284453) ^ 104666746309349151142226 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 209333492618698302284453) ^ 19030317510790754753132 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 209333492618698302284453) ^ 660358020879174455156 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 209333492618698302284453) ^ 142602312620838884 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 209333492618698302284453) ^ 20475008444 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_360610855864979553278491 : Nat.Prime 360610855864979553278491 := by
  apply lucas_primality 360610855864979553278491 (3 : ZMod 360610855864979553278491)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (12020361862165985109283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (12020361862165985109283, 1)] : List FactorBlock).map factorBlockValue).prod) = 360610855864979553278491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_12020361862165985109283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 360610855864979553278491) ^ 180305427932489776639245 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 360610855864979553278491) ^ 120203618621659851092830 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 360610855864979553278491) ^ 72122171172995910655698 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 360610855864979553278491) ^ 30 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1210444915746121514869129 : Nat.Prime 1210444915746121514869129 := by
  apply lucas_primality 1210444915746121514869129 (7 : ZMod 1210444915746121514869129)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (111031, 1), (454244353583729437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (111031, 1), (454244353583729437, 1)] : List FactorBlock).map factorBlockValue).prod) = 1210444915746121514869129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_111031
      · exact prime_fortyThreeAO_454244353583729437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1210444915746121514869129) ^ 605222457873060757434564 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1210444915746121514869129) ^ 403481638582040504956376 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1210444915746121514869129) ^ 10901864486009506488 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1210444915746121514869129) ^ 2664744 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1221408774600484299240511 : Nat.Prime 1221408774600484299240511 := by
  apply lucas_primality 1221408774600484299240511 (3 : ZMod 1221408774600484299240511)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (11, 1), (157, 1), (2273, 1), (1152405966627703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (11, 1), (157, 1), (2273, 1), (1152405966627703, 1)] : List FactorBlock).map factorBlockValue).prod) = 1221408774600484299240511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_157
      · exact prime_fortyThreeAO_2273
      · exact prime_fortyThreeAO_1152405966627703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1221408774600484299240511) ^ 610704387300242149620255 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1221408774600484299240511) ^ 407136258200161433080170 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1221408774600484299240511) ^ 244281754920096859848102 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1221408774600484299240511) ^ 111037161327316754476410 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1221408774600484299240511) ^ 7779673723569963689430 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1221408774600484299240511) ^ 537355378178831631870 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1221408774600484299240511) ^ 1059877170 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_2213211842247338158597673 : Nat.Prime 2213211842247338158597673 := by
  apply lucas_primality 2213211842247338158597673 (3 : ZMod 2213211842247338158597673)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (41, 1), (233, 1), (35531, 1), (641833, 1), (181411873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (41, 1), (233, 1), (35531, 1), (641833, 1), (181411873, 1)] : List FactorBlock).map factorBlockValue).prod) = 2213211842247338158597673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_41
      · exact prime_fortyThreeAO_233
      · exact prime_fortyThreeAO_35531
      · exact prime_fortyThreeAO_641833
      · exact prime_fortyThreeAO_181411873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2213211842247338158597673) ^ 1106605921123669079298836 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2213211842247338158597673) ^ 316173120321048308371096 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2213211842247338158597673) ^ 53980776640178979477992 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2213211842247338158597673) ^ 9498763271447803255784 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2213211842247338158597673) ^ 62289601819462952312 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2213211842247338158597673) ^ 3448267450017898984 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2213211842247338158597673) ^ 12199928293818664 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_2583598923434535625501273 : Nat.Prime 2583598923434535625501273 := by
  apply lucas_primality 2583598923434535625501273 (5 : ZMod 2583598923434535625501273)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (22661333, 1), (121804629060419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (22661333, 1), (121804629060419, 1)] : List FactorBlock).map factorBlockValue).prod) = 2583598923434535625501273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_22661333
      · exact prime_fortyThreeAO_121804629060419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2583598923434535625501273) ^ 1291799461717267812750636 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2583598923434535625501273) ^ 861199641144845208500424 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2583598923434535625501273) ^ 198738378725733509653944 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2583598923434535625501273) ^ 114009132800552184 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2583598923434535625501273) ^ 21211007688 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_2630386299809663036321651 : Nat.Prime 2630386299809663036321651 := by
  apply lucas_primality 2630386299809663036321651 (2 : ZMod 2630386299809663036321651)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (223, 1), (2633, 1), (8285363, 1), (10813897949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (223, 1), (2633, 1), (8285363, 1), (10813897949, 1)] : List FactorBlock).map factorBlockValue).prod) = 2630386299809663036321651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_223
      · exact prime_fortyThreeAO_2633
      · exact prime_fortyThreeAO_8285363
      · exact prime_fortyThreeAO_10813897949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2630386299809663036321651) ^ 1315193149904831518160825 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2630386299809663036321651) ^ 526077259961932607264330 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2630386299809663036321651) ^ 11795454259236157113550 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2630386299809663036321651) ^ 999007329969488430050 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2630386299809663036321651) ^ 317473875291844550 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2630386299809663036321651) ^ 243241272685850 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_2824461137642166648313159 : Nat.Prime 2824461137642166648313159 := by
  apply lucas_primality 2824461137642166648313159 (3 : ZMod 2824461137642166648313159)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (199, 1), (26171, 1), (191579, 1), (471805563023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (199, 1), (26171, 1), (191579, 1), (471805563023, 1)] : List FactorBlock).map factorBlockValue).prod) = 2824461137642166648313159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_199
      · exact prime_fortyThreeAO_26171
      · exact prime_fortyThreeAO_191579
      · exact prime_fortyThreeAO_471805563023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2824461137642166648313159) ^ 1412230568821083324156579 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2824461137642166648313159) ^ 941487045880722216104386 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2824461137642166648313159) ^ 14193272048453098735242 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2824461137642166648313159) ^ 107923317322309680498 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2824461137642166648313159) ^ 14743062327510670002 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2824461137642166648313159) ^ 5986493926746 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_12952223188897161147258229 : Nat.Prime 12952223188897161147258229 := by
  apply lucas_primality 12952223188897161147258229 (7 : ZMod 12952223188897161147258229)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (129765930739, 1), (639821802617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (129765930739, 1), (639821802617, 1)] : List FactorBlock).map factorBlockValue).prod) = 12952223188897161147258229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_129765930739
      · exact prime_fortyThreeAO_639821802617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 12952223188897161147258229) ^ 6476111594448580573629114 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 12952223188897161147258229) ^ 4317407729632387049086076 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 12952223188897161147258229) ^ 996324860684397011327556 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 12952223188897161147258229) ^ 99812201208252 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 12952223188897161147258229) ^ 20243485195284 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_31733755316118200688507209 : Nat.Prime 31733755316118200688507209 := by
  apply lucas_primality 31733755316118200688507209 (3 : ZMod 31733755316118200688507209)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (360610855864979553278491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (360610855864979553278491, 1)] : List FactorBlock).map factorBlockValue).prod) = 31733755316118200688507209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_360610855864979553278491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 31733755316118200688507209) ^ 15866877658059100344253604 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 31733755316118200688507209) ^ 2884886846919836426227928 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 31733755316118200688507209) ^ 88 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_52518053735972476759285691 : Nat.Prime 52518053735972476759285691 := by
  apply lucas_primality 52518053735972476759285691 (2 : ZMod 52518053735972476759285691)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (373, 1), (14079907167821039345653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (373, 1), (14079907167821039345653, 1)] : List FactorBlock).map factorBlockValue).prod) = 52518053735972476759285691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_373
      · exact prime_fortyThreeAO_14079907167821039345653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 52518053735972476759285691) ^ 26259026867986238379642845 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 52518053735972476759285691) ^ 10503610747194495351857138 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 52518053735972476759285691) ^ 140799071678210393456530 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (2 : ZMod 52518053735972476759285691) ^ 3730 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_85729301882666707424938531 : Nat.Prime 85729301882666707424938531 := by
  apply lucas_primality 85729301882666707424938531 (3 : ZMod 85729301882666707424938531)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 2), (67, 1), (137, 1), (3881, 1), (6700957, 1), (41422313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 2), (67, 1), (137, 1), (3881, 1), (6700957, 1), (41422313, 1)] : List FactorBlock).map factorBlockValue).prod) = 85729301882666707424938531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_67
      · exact prime_fortyThreeAO_137
      · exact prime_fortyThreeAO_3881
      · exact prime_fortyThreeAO_6700957
      · exact prime_fortyThreeAO_41422313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 85729301882666707424938531) ^ 42864650941333353712469265 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85729301882666707424938531) ^ 28576433960888902474979510 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85729301882666707424938531) ^ 17145860376533341484987706 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85729301882666707424938531) ^ 5042900110745100436761090 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85729301882666707424938531) ^ 1279541819144279215297590 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85729301882666707424938531) ^ 625761327610705893612690 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85729301882666707424938531) ^ 22089487730653622114130 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85729301882666707424938531) ^ 12793590808397473290 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85729301882666707424938531) ^ 2069640627810105810 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_513509858751730883868571201 : Nat.Prime 513509858751730883868571201 := by
  apply lucas_primality 513509858751730883868571201 (107 : ZMod 513509858751730883868571201)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 513509858751730883868571201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_31
      · exact prime_fortyThreeAO_37
      · exact prime_fortyThreeAO_41
      · exact prime_fortyThreeAO_43
      · exact prime_fortyThreeAO_47
      · exact prime_fortyThreeAO_53
      · exact prime_fortyThreeAO_59
      · exact prime_fortyThreeAO_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 513509858751730883868571201) ^ 256754929375865441934285600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (107 : ZMod 513509858751730883868571201) ^ 171169952917243627956190400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (107 : ZMod 513509858751730883868571201) ^ 102701971750346176773714240 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (107 : ZMod 513509858751730883868571201) ^ 73358551250247269124081600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (107 : ZMod 513509858751730883868571201) ^ 39500758365517760297582400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (107 : ZMod 513509858751730883868571201) ^ 30206462279513581404033600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (107 : ZMod 513509858751730883868571201) ^ 27026834671143730729924800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (107 : ZMod 513509858751730883868571201) ^ 22326515597901342776894400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (107 : ZMod 513509858751730883868571201) ^ 17707236508680375305812800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (107 : ZMod 513509858751730883868571201) ^ 16564834153281641415115200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (107 : ZMod 513509858751730883868571201) ^ 13878644831127861726177600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (107 : ZMod 513509858751730883868571201) ^ 12524630701261728874843200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (107 : ZMod 513509858751730883868571201) ^ 11942089738412346136478400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (107 : ZMod 513509858751730883868571201) ^ 10925741675568742209969600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (107 : ZMod 513509858751730883868571201) ^ 9688865259466620450350400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (107 : ZMod 513509858751730883868571201) ^ 8703556927995438709636800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (107 : ZMod 513509858751730883868571201) ^ 8418194405766080063419200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_726249657377447964328407841 : Nat.Prime 726249657377447964328407841 := by
  apply lucas_primality 726249657377447964328407841 (71 : ZMod 726249657377447964328407841)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 726249657377447964328407841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_31
      · exact prime_fortyThreeAO_37
      · exact prime_fortyThreeAO_41
      · exact prime_fortyThreeAO_43
      · exact prime_fortyThreeAO_47
      · exact prime_fortyThreeAO_53
      · exact prime_fortyThreeAO_59
      · exact prime_fortyThreeAO_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 726249657377447964328407841) ^ 363124828688723982164203920 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 726249657377447964328407841) ^ 242083219125815988109469280 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 726249657377447964328407841) ^ 145249931475489592865681568 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 726249657377447964328407841) ^ 103749951053921137761201120 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 726249657377447964328407841) ^ 66022696125222542211673440 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 726249657377447964328407841) ^ 55865358259803689563723680 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 726249657377447964328407841) ^ 42720568081026350842847520 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 726249657377447964328407841) ^ 38223666177760419175179360 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 726249657377447964328407841) ^ 31576072059889041927322080 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 726249657377447964328407841) ^ 25043091633705102218220960 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 726249657377447964328407841) ^ 23427408302498321429948640 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 726249657377447964328407841) ^ 19628369118309404441308320 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 726249657377447964328407841) ^ 17713406277498730837278240 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 726249657377447964328407841) ^ 16889526915754603821590880 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 726249657377447964328407841) ^ 15452120369732935411242720 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 726249657377447964328407841) ^ 13702823724102791779781280 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 726249657377447964328407841) ^ 12309316226736406175057760 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 726249657377447964328407841) ^ 11905732088154884661121440 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_833401246170841926278500801 : Nat.Prime 833401246170841926278500801 := by
  apply lucas_primality 833401246170841926278500801 (131 : ZMod 833401246170841926278500801)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) = 833401246170841926278500801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_31
      · exact prime_fortyThreeAO_37
      · exact prime_fortyThreeAO_41
      · exact prime_fortyThreeAO_43
      · exact prime_fortyThreeAO_47
      · exact prime_fortyThreeAO_53
      · exact prime_fortyThreeAO_59
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (131 : ZMod 833401246170841926278500801) ^ 416700623085420963139250400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (131 : ZMod 833401246170841926278500801) ^ 277800415390280642092833600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (131 : ZMod 833401246170841926278500801) ^ 166680249234168385255700160 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (131 : ZMod 833401246170841926278500801) ^ 119057320881548846611214400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (131 : ZMod 833401246170841926278500801) ^ 75763749651894720570772800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (131 : ZMod 833401246170841926278500801) ^ 64107788166987840482961600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (131 : ZMod 833401246170841926278500801) ^ 49023602715931878016382400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (131 : ZMod 833401246170841926278500801) ^ 43863223482675890856763200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (131 : ZMod 833401246170841926278500801) ^ 36234836790036605490369600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (131 : ZMod 833401246170841926278500801) ^ 28737974005891100906155200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (131 : ZMod 833401246170841926278500801) ^ 26883911166801352460596800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (131 : ZMod 833401246170841926278500801) ^ 22524358004617349358878400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (131 : ZMod 833401246170841926278500801) ^ 20326859662703461616548800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (131 : ZMod 833401246170841926278500801) ^ 19381424329554463401825600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (131 : ZMod 833401246170841926278500801) ^ 17731941407890253750606400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (131 : ZMod 833401246170841926278500801) ^ 15724551814544187288273600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (131 : ZMod 833401246170841926278500801) ^ 14125444850353252987771200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_891885544147743114087518401 : Nat.Prime 891885544147743114087518401 := by
  apply lucas_primality 891885544147743114087518401 (76 : ZMod 891885544147743114087518401)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 891885544147743114087518401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_31
      · exact prime_fortyThreeAO_37
      · exact prime_fortyThreeAO_41
      · exact prime_fortyThreeAO_43
      · exact prime_fortyThreeAO_47
      · exact prime_fortyThreeAO_53
      · exact prime_fortyThreeAO_59
      · exact prime_fortyThreeAO_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (76 : ZMod 891885544147743114087518401) ^ 445942772073871557043759200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (76 : ZMod 891885544147743114087518401) ^ 297295181382581038029172800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (76 : ZMod 891885544147743114087518401) ^ 178377108829548622817503680 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (76 : ZMod 891885544147743114087518401) ^ 127412220592534730583931200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (76 : ZMod 891885544147743114087518401) ^ 81080504013431192189774400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (76 : ZMod 891885544147743114087518401) ^ 68606580319057162622116800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (76 : ZMod 891885544147743114087518401) ^ 52463855538102536122795200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (76 : ZMod 891885544147743114087518401) ^ 38777632354249700612500800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (76 : ZMod 891885544147743114087518401) ^ 30754673936129072899569600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (76 : ZMod 891885544147743114087518401) ^ 28770501424120745615726400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (76 : ZMod 891885544147743114087518401) ^ 24105014706695759840203200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (76 : ZMod 891885544147743114087518401) ^ 21753305954823002782622400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (76 : ZMod 891885544147743114087518401) ^ 20741524282505653815988800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (76 : ZMod 891885544147743114087518401) ^ 18976288173356236469947200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (76 : ZMod 891885544147743114087518401) ^ 16828029134863077624292800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (76 : ZMod 891885544147743114087518401) ^ 15116704138097340916737600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (76 : ZMod 891885544147743114087518401) ^ 14621074494225296952254400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_959197660687195424584689601 : Nat.Prime 959197660687195424584689601 := by
  apply lucas_primality 959197660687195424584689601 (71 : ZMod 959197660687195424584689601)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 959197660687195424584689601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_31
      · exact prime_fortyThreeAO_37
      · exact prime_fortyThreeAO_41
      · exact prime_fortyThreeAO_43
      · exact prime_fortyThreeAO_47
      · exact prime_fortyThreeAO_59
      · exact prime_fortyThreeAO_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 959197660687195424584689601) ^ 479598830343597712292344800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 959197660687195424584689601) ^ 319732553562398474861563200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 959197660687195424584689601) ^ 191839532137439084916937920 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 959197660687195424584689601) ^ 137028237241027917797812800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 959197660687195424584689601) ^ 87199787335199584053153600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 959197660687195424584689601) ^ 73784435437476571121899200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 959197660687195424584689601) ^ 56423391805129142622628800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 959197660687195424584689601) ^ 50484087404589232872878400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 959197660687195424584689601) ^ 41704246116834583677595200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 959197660687195424584689601) ^ 33075781403006738778782400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 959197660687195424584689601) ^ 30941860022167594341441600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 959197660687195424584689601) ^ 25924261099653930394180800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 959197660687195424584689601) ^ 23395064894809644502065600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 959197660687195424584689601) ^ 22306922341562684292667200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 959197660687195424584689601) ^ 20408460865685009033716800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 959197660687195424584689601) ^ 16257587469274498721774400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (71 : ZMod 959197660687195424584689601) ^ 15724551814544187288273600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_1588671125513167421968392151 : Nat.Prime 1588671125513167421968392151 := by
  apply lucas_primality 1588671125513167421968392151 (14 : ZMod 1588671125513167421968392151)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1588671125513167421968392151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_31
      · exact prime_fortyThreeAO_37
      · exact prime_fortyThreeAO_41
      · exact prime_fortyThreeAO_43
      · exact prime_fortyThreeAO_47
      · exact prime_fortyThreeAO_53
      · exact prime_fortyThreeAO_59
      · exact prime_fortyThreeAO_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1588671125513167421968392151) ^ 794335562756583710984196075 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1588671125513167421968392151) ^ 529557041837722473989464050 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1588671125513167421968392151) ^ 317734225102633484393678430 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1588671125513167421968392151) ^ 226953017930452488852627450 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1588671125513167421968392151) ^ 144424647773924311088035650 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1588671125513167421968392151) ^ 122205471193320570920645550 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1588671125513167421968392151) ^ 93451242677245142468728950 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1588671125513167421968392151) ^ 83614269763850916945704850 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1588671125513167421968392151) ^ 69072657631007279216017050 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1588671125513167421968392151) ^ 54781762948729911102358350 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1588671125513167421968392151) ^ 51247455661715078128012650 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1588671125513167421968392151) ^ 42937057446301822215361950 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1588671125513167421968392151) ^ 38748076232028473706546150 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1588671125513167421968392151) ^ 36945840128213195859730050 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1588671125513167421968392151) ^ 33801513308790796212093450 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1588671125513167421968392151) ^ 29974926896474857018271550 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1588671125513167421968392151) ^ 26926629245985888507938850 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1588671125513167421968392151) ^ 26043788942838810196203150 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_3910575078186258269460657601 : Nat.Prime 3910575078186258269460657601 := by
  apply lucas_primality 3910575078186258269460657601 (26 : ZMod 3910575078186258269460657601)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 3910575078186258269460657601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_31
      · exact prime_fortyThreeAO_37
      · exact prime_fortyThreeAO_41
      · exact prime_fortyThreeAO_43
      · exact prime_fortyThreeAO_47
      · exact prime_fortyThreeAO_53
      · exact prime_fortyThreeAO_59
      · exact prime_fortyThreeAO_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 3910575078186258269460657601) ^ 1955287539093129134730328800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3910575078186258269460657601) ^ 1303525026062086089820219200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3910575078186258269460657601) ^ 782115015637251653892131520 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3910575078186258269460657601) ^ 558653582598036895637236800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3910575078186258269460657601) ^ 355506825289659842678241600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3910575078186258269460657601) ^ 230033828128603427615332800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3910575078186258269460657601) ^ 205819740957171487866350400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3910575078186258269460657601) ^ 170025003399402533454811200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3910575078186258269460657601) ^ 134847416489181319636574400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3910575078186258269460657601) ^ 126147583167298653853569600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3910575078186258269460657601) ^ 105691218329358331607044800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3910575078186258269460657601) ^ 95379879955762396816113600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3910575078186258269460657601) ^ 90943606469447866731643200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3910575078186258269460657601) ^ 83203725067792729137460800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3910575078186258269460657601) ^ 73784435437476571121899200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3910575078186258269460657601) ^ 66280933528580648634926400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3910575078186258269460657601) ^ 64107788166987840482961600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_7262496573774479643284078401 : Nat.Prime 7262496573774479643284078401 := by
  apply lucas_primality 7262496573774479643284078401 (83 : ZMod 7262496573774479643284078401)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 7262496573774479643284078401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_31
      · exact prime_fortyThreeAO_37
      · exact prime_fortyThreeAO_41
      · exact prime_fortyThreeAO_43
      · exact prime_fortyThreeAO_47
      · exact prime_fortyThreeAO_53
      · exact prime_fortyThreeAO_59
      · exact prime_fortyThreeAO_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 7262496573774479643284078401) ^ 3631248286887239821642039200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (83 : ZMod 7262496573774479643284078401) ^ 2420832191258159881094692800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (83 : ZMod 7262496573774479643284078401) ^ 1452499314754895928656815680 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (83 : ZMod 7262496573774479643284078401) ^ 1037499510539211377612011200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (83 : ZMod 7262496573774479643284078401) ^ 660226961252225422116734400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (83 : ZMod 7262496573774479643284078401) ^ 558653582598036895637236800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (83 : ZMod 7262496573774479643284078401) ^ 427205680810263508428475200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (83 : ZMod 7262496573774479643284078401) ^ 382236661777604191751793600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (83 : ZMod 7262496573774479643284078401) ^ 315760720598890419273220800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (83 : ZMod 7262496573774479643284078401) ^ 250430916337051022182209600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (83 : ZMod 7262496573774479643284078401) ^ 234274083024983214299486400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (83 : ZMod 7262496573774479643284078401) ^ 196283691183094044413083200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (83 : ZMod 7262496573774479643284078401) ^ 177134062774987308372782400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (83 : ZMod 7262496573774479643284078401) ^ 168895269157546038215908800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (83 : ZMod 7262496573774479643284078401) ^ 154521203697329354112427200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (83 : ZMod 7262496573774479643284078401) ^ 137028237241027917797812800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (83 : ZMod 7262496573774479643284078401) ^ 123093162267364061750577600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (83 : ZMod 7262496573774479643284078401) ^ 119057320881548846611214400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_12709369004105339375747137201 : Nat.Prime 12709369004105339375747137201 := by
  apply lucas_primality 12709369004105339375747137201 (79 : ZMod 12709369004105339375747137201)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 12709369004105339375747137201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_31
      · exact prime_fortyThreeAO_37
      · exact prime_fortyThreeAO_41
      · exact prime_fortyThreeAO_43
      · exact prime_fortyThreeAO_47
      · exact prime_fortyThreeAO_53
      · exact prime_fortyThreeAO_59
      · exact prime_fortyThreeAO_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 12709369004105339375747137201) ^ 6354684502052669687873568600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (79 : ZMod 12709369004105339375747137201) ^ 4236456334701779791915712400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (79 : ZMod 12709369004105339375747137201) ^ 2541873800821067875149427440 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (79 : ZMod 12709369004105339375747137201) ^ 1815624143443619910821019600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (79 : ZMod 12709369004105339375747137201) ^ 1155397182191394488704285200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (79 : ZMod 12709369004105339375747137201) ^ 977643769546564567365164400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (79 : ZMod 12709369004105339375747137201) ^ 747609941417961139749831600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (79 : ZMod 12709369004105339375747137201) ^ 668914158110807335565638800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (79 : ZMod 12709369004105339375747137201) ^ 552581261048058233728136400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (79 : ZMod 12709369004105339375747137201) ^ 438254103589839288818866800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (79 : ZMod 12709369004105339375747137201) ^ 409979645293720625024101200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (79 : ZMod 12709369004105339375747137201) ^ 343496459570414577722895600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (79 : ZMod 12709369004105339375747137201) ^ 309984609856227789652369200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (79 : ZMod 12709369004105339375747137201) ^ 295566721025705566877840400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (79 : ZMod 12709369004105339375747137201) ^ 270412106470326369696747600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (79 : ZMod 12709369004105339375747137201) ^ 239799415171798856146172400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (79 : ZMod 12709369004105339375747137201) ^ 215413033967887108063510800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (79 : ZMod 12709369004105339375747137201) ^ 208350311542710481569625200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_50837476016421357502988548801 : Nat.Prime 50837476016421357502988548801 := by
  apply lucas_primality 50837476016421357502988548801 (67 : ZMod 50837476016421357502988548801)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_5
      · exact prime_fortyThreeAO_7
      · exact prime_fortyThreeAO_11
      · exact prime_fortyThreeAO_13
      · exact prime_fortyThreeAO_17
      · exact prime_fortyThreeAO_19
      · exact prime_fortyThreeAO_23
      · exact prime_fortyThreeAO_29
      · exact prime_fortyThreeAO_31
      · exact prime_fortyThreeAO_37
      · exact prime_fortyThreeAO_41
      · exact prime_fortyThreeAO_43
      · exact prime_fortyThreeAO_47
      · exact prime_fortyThreeAO_53
      · exact prime_fortyThreeAO_59
      · exact prime_fortyThreeAO_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 50837476016421357502988548801) ^ 25418738008210678751494274400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (67 : ZMod 50837476016421357502988548801) ^ 16945825338807119167662849600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (67 : ZMod 50837476016421357502988548801) ^ 10167495203284271500597709760 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (67 : ZMod 50837476016421357502988548801) ^ 7262496573774479643284078400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (67 : ZMod 50837476016421357502988548801) ^ 4621588728765577954817140800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (67 : ZMod 50837476016421357502988548801) ^ 3910575078186258269460657600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (67 : ZMod 50837476016421357502988548801) ^ 2990439765671844558999326400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (67 : ZMod 50837476016421357502988548801) ^ 2675656632443229342262555200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (67 : ZMod 50837476016421357502988548801) ^ 2210325044192232934912545600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (67 : ZMod 50837476016421357502988548801) ^ 1753016414359357155275467200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (67 : ZMod 50837476016421357502988548801) ^ 1639918581174882500096404800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (67 : ZMod 50837476016421357502988548801) ^ 1373985838281658310891582400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (67 : ZMod 50837476016421357502988548801) ^ 1239938439424911158609476800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (67 : ZMod 50837476016421357502988548801) ^ 1182266884102822267511361600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (67 : ZMod 50837476016421357502988548801) ^ 1081648425881305478786990400 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (67 : ZMod 50837476016421357502988548801) ^ 959197660687195424584689600 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (67 : ZMod 50837476016421357502988548801) ^ 861652135871548432254043200 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (67 : ZMod 50837476016421357502988548801) ^ 833401246170841926278500800 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem prime_fortyThreeAO_50837476016421357502988548873 : Nat.Prime 50837476016421357502988548873 := by
  apply lucas_primality 50837476016421357502988548873 (7 : ZMod 50837476016421357502988548873)
  · rw [← fortyThreeAOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (401587, 1), (779981, 1), (2254175965482383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (401587, 1), (779981, 1), (2254175965482383, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyThreeAO_2
      · exact prime_fortyThreeAO_3
      · exact prime_fortyThreeAO_401587
      · exact prime_fortyThreeAO_779981
      · exact prime_fortyThreeAO_2254175965482383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 50837476016421357502988548873) ^ 25418738008210678751494274436 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 50837476016421357502988548873) ^ 16945825338807119167662849624 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 50837476016421357502988548873) ^ 126591438508769849380056 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 50837476016421357502988548873) ^ 65177838968412509411112 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide
    · change (7 : ZMod 50837476016421357502988548873) ^ 22552576548984 ≠ 1
      rw [← fortyThreeAOFastPow_eq_pow]
      decide

private theorem phi_fortyThreeAO_50837476016421357502988548800 : Nat.totient 50837476016421357502988548800 = 6689568843752507493580800000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 2), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548800 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_3, prime_fortyThreeAO_5, prime_fortyThreeAO_7, prime_fortyThreeAO_11, prime_fortyThreeAO_13, prime_fortyThreeAO_17, prime_fortyThreeAO_19, prime_fortyThreeAO_23, prime_fortyThreeAO_29, prime_fortyThreeAO_31, prime_fortyThreeAO_37, prime_fortyThreeAO_41, prime_fortyThreeAO_43, prime_fortyThreeAO_47, prime_fortyThreeAO_53, prime_fortyThreeAO_59, prime_fortyThreeAO_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548801 : Nat.totient 50837476016421357502988548801 = 50837476016421357502988548800 := by
  rw [← show ((([(50837476016421357502988548801, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548801 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_50837476016421357502988548801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548802 : Nat.totient 50837476016421357502988548802 = 25415414282445792815480832000 := by
  rw [← show ((([(2, 1), (9601, 1), (37589, 1), (434336989, 1), (162162311681, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548802 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_9601, prime_fortyThreeAO_37589, prime_fortyThreeAO_434336989, prime_fortyThreeAO_162162311681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548803 : Nat.totient 50837476016421357502988548803 = 33891650677606626566499761504 := by
  rw [← show ((([(3, 1), (4457754116957, 1), (3801426658851893, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548803 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3, prime_fortyThreeAO_4457754116957, prime_fortyThreeAO_3801426658851893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548804 : Nat.totient 50837476016421357502988548804 = 25418738008210678751494274400 := by
  rw [← show ((([(2, 2), (12709369004105339375747137201, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548804 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_12709369004105339375747137201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548805 : Nat.totient 50837476016421357502988548805 = 40669980813136172454599704768 := by
  rw [← show ((([(5, 1), (60596325868877, 1), (167790621914693, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548805 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_5, prime_fortyThreeAO_60596325868877, prime_fortyThreeAO_167790621914693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548806 : Nat.totient 50837476016421357502988548806 = 16753527854552245508899209216 := by
  rw [← show ((([(2, 1), (3, 1), (97, 1), (953, 1), (1610610409, 1), (56908559640929, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548806 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_3, prime_fortyThreeAO_97, prime_fortyThreeAO_953, prime_fortyThreeAO_1610610409, prime_fortyThreeAO_56908559640929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548807 : Nat.totient 50837476016421357502988548807 = 43574979442646877859704470400 := by
  rw [← show ((([(7, 1), (7262496573774479643284078401, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548807 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_7, prime_fortyThreeAO_7262496573774479643284078401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548808 : Nat.totient 50837476016421357502988548808 = 25083582481275490268628150528 := by
  rw [← show ((([(2, 3), (79, 1), (1873, 1), (42946633384826817384103, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548808 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_79, prime_fortyThreeAO_1873, prime_fortyThreeAO_42946633384826817384103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548809 : Nat.totient 50837476016421357502988548809 = 33862602806474498192316918528 := by
  rw [← show ((([(3, 2), (1229, 1), (23017, 1), (199682897777824588157, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548809 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3, prime_fortyThreeAO_1229, prime_fortyThreeAO_23017, prime_fortyThreeAO_199682897777824588157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548810 : Nat.totient 50837476016421357502988548810 = 20326137559199553648561019648 := by
  rw [← show ((([(2, 1), (5, 1), (2297, 1), (2213211842247338158597673, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548810 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_5, prime_fortyThreeAO_2297, prime_fortyThreeAO_2213211842247338158597673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548811 : Nat.totient 50837476016421357502988548811 = 46215887195099053202192816040 := by
  rw [← show ((([(11, 1), (499324999, 1), (9255672634098534199, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548811 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_11, prime_fortyThreeAO_499324999, prime_fortyThreeAO_9255672634098534199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548812 : Nat.totient 50837476016421357502988548812 = 16945825154934846674387287872 := by
  rw [← show ((([(2, 2), (3, 1), (112885027, 1), (505419127, 1), (74253122269, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548812 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_3, prime_fortyThreeAO_112885027, prime_fortyThreeAO_505419127, prime_fortyThreeAO_74253122269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548813 : Nat.totient 50837476016421357502988548813 = 46926900938235099233527891200 := by
  rw [← show ((([(13, 1), (3910575078186258269460657601, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548813 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_13, prime_fortyThreeAO_3910575078186258269460657601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548814 : Nat.totient 50837476016421357502988548814 = 21787180156387997213494701600 := by
  rw [← show ((([(2, 1), (7, 1), (70381, 1), (51594155906952726185221, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548814 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_7, prime_fortyThreeAO_70381, prime_fortyThreeAO_51594155906952726185221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548815 : Nat.totient 50837476016421357502988548815 = 26869228041083566735826804736 := by
  rw [← show ((([(3, 1), (5, 1), (113, 1), (6473, 1), (4633494704020955437129, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548815 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3, prime_fortyThreeAO_5, prime_fortyThreeAO_113, prime_fortyThreeAO_6473, prime_fortyThreeAO_4633494704020955437129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548816 : Nat.totient 50837476016421357502988548816 = 25110901165919840749957939200 := by
  rw [← show ((([(2, 4), (109, 1), (641, 1), (829, 1), (5011, 1), (26356279, 1), (415352129, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548816 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_109, prime_fortyThreeAO_641, prime_fortyThreeAO_829, prime_fortyThreeAO_5011, prime_fortyThreeAO_26356279, prime_fortyThreeAO_415352129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548817 : Nat.totient 50837476016421357502988548817 = 47847036245962924283233635072 := by
  rw [← show ((([(17, 1), (9996062173, 1), (299161781301162037, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548817 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_17, prime_fortyThreeAO_9996062173, prime_fortyThreeAO_299161781301162037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548818 : Nat.totient 50837476016421357502988548818 = 16755422806910409963531805824 := by
  rw [← show ((([(2, 1), (3, 2), (89, 1), (31733755316118200688507209, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548818 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_3, prime_fortyThreeAO_89, prime_fortyThreeAO_31733755316118200688507209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548819 : Nat.totient 50837476016421357502988548819 = 47581321827016106286299313120 := by
  rw [← show ((([(19, 1), (83, 1), (202757, 1), (158992423920783882271, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548819 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_19, prime_fortyThreeAO_83, prime_fortyThreeAO_202757, prime_fortyThreeAO_158992423920783882271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548820 : Nat.totient 50837476016421357502988548820 = 20244621709119743340126907392 := by
  rw [← show ((([(2, 2), (5, 1), (227, 1), (25717, 1), (6204369463, 1), (70179484073, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548820 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_5, prime_fortyThreeAO_227, prime_fortyThreeAO_25717, prime_fortyThreeAO_6204369463, prime_fortyThreeAO_70179484073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548821 : Nat.totient 50837476016421357502988548821 = 29018983108016704145630287104 := by
  rw [← show ((([(3, 1), (7, 1), (937, 1), (2583598923434535625501273, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548821 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3, prime_fortyThreeAO_7, prime_fortyThreeAO_937, prime_fortyThreeAO_2583598923434535625501273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548822 : Nat.totient 50837476016421357502988548822 = 22978550790797484592200746880 := by
  rw [← show ((([(2, 1), (11, 1), (229, 1), (863, 1), (12589, 1), (928803381995832767, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548822 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_11, prime_fortyThreeAO_229, prime_fortyThreeAO_863, prime_fortyThreeAO_12589, prime_fortyThreeAO_928803381995832767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548823 : Nat.totient 50837476016421357502988548823 = 48400892190898498905077942496 := by
  rw [← show ((([(23, 1), (347, 1), (563, 1), (153636319, 1), (73641797680639, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548823 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_23, prime_fortyThreeAO_347, prime_fortyThreeAO_563, prime_fortyThreeAO_153636319, prime_fortyThreeAO_73641797680639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548824 : Nat.totient 50837476016421357502988548824 = 16938831595185718123902796800 := by
  rw [← show ((([(2, 3), (3, 1), (2423, 1), (2655507551, 1), (329209064005537, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548824 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_3, prime_fortyThreeAO_2423, prime_fortyThreeAO_2655507551, prime_fortyThreeAO_329209064005537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548825 : Nat.totient 50837476016421357502988548825 = 40410936349359142779445671360 := by
  rw [← show ((([(5, 2), (157, 1), (12952223188897161147258229, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548825 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_5, prime_fortyThreeAO_157, prime_fortyThreeAO_12952223188897161147258229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548826 : Nat.totient 50837476016421357502988548826 = 22883366922671629649670912000 := by
  rw [← show ((([(2, 1), (13, 1), (67, 1), (101, 1), (22031, 1), (13115360895995606113, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548826 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_13, prime_fortyThreeAO_67, prime_fortyThreeAO_101, prime_fortyThreeAO_22031, prime_fortyThreeAO_13115360895995606113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548827 : Nat.totient 50837476016421357502988548827 = 33574856563271663229806583840 := by
  rw [← show ((([(3, 3), (107, 1), (675341, 1), (26056334574040524623, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548827 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3, prime_fortyThreeAO_107, prime_fortyThreeAO_675341, prime_fortyThreeAO_26056334574040524623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548828 : Nat.totient 50837476016421357502988548828 = 21787489721322384437522576304 := by
  rw [← show ((([(2, 2), (7, 1), (33220292875087, 1), (54654067929823, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548828 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_7, prime_fortyThreeAO_33220292875087, prime_fortyThreeAO_54654067929823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548829 : Nat.totient 50837476016421357502988548829 = 49084459602059393894145761536 := by
  rw [← show ((([(29, 1), (26213782231913, 1), (66873845172377, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548829 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_29, prime_fortyThreeAO_26213782231913, prime_fortyThreeAO_66873845172377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548830 : Nat.totient 50837476016421357502988548830 = 13496720700372654787166822400 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (317, 1), (787, 1), (5041601, 1), (1347287434223959, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548830 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_3, prime_fortyThreeAO_5, prime_fortyThreeAO_317, prime_fortyThreeAO_787, prime_fortyThreeAO_5041601, prime_fortyThreeAO_1347287434223959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548831 : Nat.totient 50837476016421357502988548831 = 48915734703945324463893024000 := by
  rw [← show ((([(31, 1), (179, 1), (7013, 1), (1272927463, 1), (1026270299401, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548831 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_31, prime_fortyThreeAO_179, prime_fortyThreeAO_7013, prime_fortyThreeAO_1272927463, prime_fortyThreeAO_1026270299401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548832 : Nat.totient 50837476016421357502988548832 = 25418738008210678751494274400 := by
  rw [← show ((([(2, 5), (1588671125513167421968392151, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548832 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_1588671125513167421968392151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548833 : Nat.totient 50837476016421357502988548833 = 30804789716016370808380704000 := by
  rw [← show ((([(3, 1), (11, 1), (5413, 1), (284227, 1), (21028771, 1), (47615986981, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548833 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3, prime_fortyThreeAO_11, prime_fortyThreeAO_5413, prime_fortyThreeAO_284227, prime_fortyThreeAO_21028771, prime_fortyThreeAO_47615986981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548834 : Nat.totient 50837476016421357502988548834 = 23923518119559716035860467712 := by
  rw [← show ((([(2, 1), (17, 1), (4114076017, 1), (363440023144307953, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548834 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_17, prime_fortyThreeAO_4114076017, prime_fortyThreeAO_363440023144307953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548835 : Nat.totient 50837476016421357502988548835 = 34859961950970137818720491648 := by
  rw [← show ((([(5, 1), (7, 1), (1613653, 1), (900131140186208514877, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548835 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_5, prime_fortyThreeAO_7, prime_fortyThreeAO_1613653, prime_fortyThreeAO_900131140186208514877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548836 : Nat.totient 50837476016421357502988548836 = 16801872288602943220513367040 := by
  rw [← show ((([(2, 2), (3, 2), (149, 1), (557, 1), (6111439, 1), (31047293, 1), (89675291, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548836 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_3, prime_fortyThreeAO_149, prime_fortyThreeAO_557, prime_fortyThreeAO_6111439, prime_fortyThreeAO_31047293, prime_fortyThreeAO_89675291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548837 : Nat.totient 50837476016421357502988548837 = 49228252874699818121184407040 := by
  rw [← show ((([(37, 1), (211, 1), (60539, 1), (107563409109560591969, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548837 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_37, prime_fortyThreeAO_211, prime_fortyThreeAO_60539, prime_fortyThreeAO_107563409109560591969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548838 : Nat.totient 50837476016421357502988548838 = 23905117099765296730440951552 := by
  rw [← show ((([(2, 1), (19, 3), (137, 1), (1327973, 1), (15842063, 1), (1285794707, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548838 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_19, prime_fortyThreeAO_137, prime_fortyThreeAO_1327973, prime_fortyThreeAO_15842063, prime_fortyThreeAO_1285794707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548839 : Nat.totient 50837476016421357502988548839 = 31283771814694409252530033152 := by
  rw [← show ((([(3, 1), (13, 1), (37747, 1), (2269153009, 1), (15218545638187, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548839 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3, prime_fortyThreeAO_13, prime_fortyThreeAO_37747, prime_fortyThreeAO_2269153009, prime_fortyThreeAO_15218545638187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548840 : Nat.totient 50837476016421357502988548840 = 20330478192128978908202108928 := by
  rw [← show ((([(2, 3), (5, 1), (4507, 1), (58734107, 1), (4801158693898529, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548840 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_5, prime_fortyThreeAO_4507, prime_fortyThreeAO_58734107, prime_fortyThreeAO_4801158693898529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548841 : Nat.totient 50837476016421357502988548841 = 49484559131490759678446528160 := by
  rw [← show ((([(41, 1), (439, 1), (2824461137642166648313159, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548841 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_41, prime_fortyThreeAO_439, prime_fortyThreeAO_2824461137642166648313159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548842 : Nat.totient 50837476016421357502988548842 = 14510336242253753474977258800 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (991, 1), (1221408774600484299240511, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548842 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_3, prime_fortyThreeAO_7, prime_fortyThreeAO_991, prime_fortyThreeAO_1221408774600484299240511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548843 : Nat.totient 50837476016421357502988548843 = 49163302769838416859041000064 := by
  rw [← show ((([(43, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548843 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_43, prime_fortyThreeAO_103, prime_fortyThreeAO_5009, prime_fortyThreeAO_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548844 : Nat.totient 50837476016421357502988548844 = 23107937303906054213491682000 := by
  rw [← show ((([(2, 2), (11, 1), (3644831, 1), (316996091778026056271, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548844 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_11, prime_fortyThreeAO_3644831, prime_fortyThreeAO_316996091778026056271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548845 : Nat.totient 50837476016421357502988548845 = 26896559183431314280074436608 := by
  rw [← show ((([(3, 2), (5, 1), (173, 1), (449, 1), (14543837805963257392933, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548845 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3, prime_fortyThreeAO_5, prime_fortyThreeAO_173, prime_fortyThreeAO_449, prime_fortyThreeAO_14543837805963257392933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548846 : Nat.totient 50837476016421357502988548846 = 24313438849239348791161177944 := by
  rw [← show ((([(2, 1), (23, 1), (177943, 1), (6210767055158766950407, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548846 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_23, prime_fortyThreeAO_177943, prime_fortyThreeAO_6210767055158766950407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548847 : Nat.totient 50837476016421357502988548847 = 49755827590505259727408682400 := by
  rw [← show ((([(47, 1), (1432795928341, 1), (754921482177661, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548847 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_47, prime_fortyThreeAO_1432795928341, prime_fortyThreeAO_754921482177661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548848 : Nat.totient 50837476016421357502988548848 = 16945587158344994171257538752 := by
  rw [← show ((([(2, 4), (3, 1), (71147, 1), (14886278882812275260783, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548848 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_3, prime_fortyThreeAO_71147, prime_fortyThreeAO_14886278882812275260783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548849 : Nat.totient 50837476016421357502988548849 = 43574979442357662218362634184 := by
  rw [← show ((([(7, 2), (150669350707, 1), (6885936029264443, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548849 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_7, prime_fortyThreeAO_150669350707, prime_fortyThreeAO_6885936029264443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548850 : Nat.totient 50837476016421357502988548850 = 20334989628496067786778316800 := by
  rw [← show ((([(2, 1), (5, 2), (29324153, 1), (240719249, 1), (144038198041, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548850 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_5, prime_fortyThreeAO_29324153, prime_fortyThreeAO_240719249, prime_fortyThreeAO_144038198041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548851 : Nat.totient 50837476016421357502988548851 = 31898004333149291875227749376 := by
  rw [← show ((([(3, 1), (17, 1), (1608527, 1), (11141154919, 1), (55623105977, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548851 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3, prime_fortyThreeAO_17, prime_fortyThreeAO_1608527, prime_fortyThreeAO_11141154919, prime_fortyThreeAO_55623105977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548852 : Nat.totient 50837476016421357502988548852 = 23132965120513801748399957760 := by
  rw [← show ((([(2, 2), (13, 1), (71, 1), (1627337, 1), (8461449937532218063, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548852 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_13, prime_fortyThreeAO_71, prime_fortyThreeAO_1627337, prime_fortyThreeAO_8461449937532218063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548853 : Nat.totient 50837476016421357502988548853 = 49878278355734162078403859200 := by
  rw [← show ((([(53, 1), (959197660687195424584689601, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548853 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_53, prime_fortyThreeAO_959197660687195424584689601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548854 : Nat.totient 50837476016421357502988548854 = 16931354095990033668800437320 := by
  rw [← show ((([(2, 1), (3, 5), (1171, 1), (89328659364725301618659, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548854 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_3, prime_fortyThreeAO_1171, prime_fortyThreeAO_89328659364725301618659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548855 : Nat.totient 50837476016421357502988548855 = 36187797190263411078002073600 := by
  rw [← show ((([(5, 1), (11, 1), (73, 1), (131, 1), (532709, 1), (35383199, 1), (5127905417, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548855 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_5, prime_fortyThreeAO_11, prime_fortyThreeAO_73, prime_fortyThreeAO_131, prime_fortyThreeAO_532709, prime_fortyThreeAO_35383199, prime_fortyThreeAO_5127905417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548856 : Nat.totient 50837476016421357502988548856 = 21752361905065446220411507200 := by
  rw [← show ((([(2, 3), (7, 1), (733, 1), (4027, 1), (19408331, 1), (15846091487381, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548856 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_7, prime_fortyThreeAO_733, prime_fortyThreeAO_4027, prime_fortyThreeAO_19408331, prime_fortyThreeAO_15846091487381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548857 : Nat.totient 50837476016421357502988548857 = 32107879589318752107150662400 := by
  rw [← show ((([(3, 1), (19, 1), (891885544147743114087518401, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548857 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3, prime_fortyThreeAO_19, prime_fortyThreeAO_891885544147743114087518401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548858 : Nat.totient 50837476016421357502988548858 = 24534797629138375461719973696 := by
  rw [← show ((([(2, 1), (29, 1), (3343, 1), (270229, 1), (970258947223505683, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548858 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_29, prime_fortyThreeAO_3343, prime_fortyThreeAO_270229, prime_fortyThreeAO_970258947223505683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548859 : Nat.totient 50837476016421357502988548859 = 49975823867728246582467304456 := by
  rw [← show ((([(59, 1), (3897795203, 1), (221061418313708267, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548859 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_59, prime_fortyThreeAO_3897795203, prime_fortyThreeAO_221061418313708267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548860 : Nat.totient 50837476016421357502988548860 = 13556617913497817183645912832 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (320053, 1), (2647346742384404952877, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548860 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_3, prime_fortyThreeAO_5, prime_fortyThreeAO_320053, prime_fortyThreeAO_2647346742384404952877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548861 : Nat.totient 50837476016421357502988548861 = 50004074770250515576710048000 := by
  rw [← show ((([(61, 1), (833401246170841926278500801, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548861 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_61, prime_fortyThreeAO_833401246170841926278500801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548862 : Nat.totient 50837476016421357502988548862 = 24592498712844676552377420960 := by
  rw [← show ((([(2, 1), (31, 1), (3917, 1), (209333492618698302284453, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548862 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_31, prime_fortyThreeAO_3917, prime_fortyThreeAO_209333492618698302284453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548863 : Nat.totient 50837476016421357502988548863 = 29049982424475332287198777344 := by
  rw [← show ((([(3, 2), (7, 1), (7505249, 1), (107517294063490759649, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548863 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3, prime_fortyThreeAO_7, prime_fortyThreeAO_7505249, prime_fortyThreeAO_107517294063490759649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548864 : Nat.totient 50837476016421357502988548864 = 25418738008111495196907583488 := by
  rw [← show ((([(2, 8), (256364582137, 1), (774615155626387, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548864 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_256364582137, prime_fortyThreeAO_774615155626387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548865 : Nat.totient 50837476016421357502988548865 = 37462664678052302574770119680 := by
  rw [← show ((([(5, 1), (13, 1), (479, 1), (77839, 1), (20976733589071979441, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548865 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_5, prime_fortyThreeAO_13, prime_fortyThreeAO_479, prime_fortyThreeAO_77839, prime_fortyThreeAO_20976733589071979441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548866 : Nat.totient 50837476016421357502988548866 = 15405247014787446785164492800 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (383297, 1), (1800473, 1), (1116138301851721, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548866 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_3, prime_fortyThreeAO_11, prime_fortyThreeAO_383297, prime_fortyThreeAO_1800473, prime_fortyThreeAO_1116138301851721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548867 : Nat.totient 50837476016421357502988548867 = 50821846185176073789437426112 := by
  rw [← show ((([(3253, 1), (25973737, 1), (601679865410253247, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548867 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3253, prime_fortyThreeAO_25973737, prime_fortyThreeAO_601679865410253247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548868 : Nat.totient 50837476016421357502988548868 = 23907030518120880003013596800 := by
  rw [← show ((([(2, 2), (17, 3), (1451, 1), (1782829504095638945459, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548868 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_17, prime_fortyThreeAO_1451, prime_fortyThreeAO_1782829504095638945459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548869 : Nat.totient 50837476016421357502988548869 = 32393559332645468592211906560 := by
  rw [← show ((([(3, 1), (23, 1), (1321, 1), (43793137, 1), (12735793724305513, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548869 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3, prime_fortyThreeAO_23, prime_fortyThreeAO_1321, prime_fortyThreeAO_43793137, prime_fortyThreeAO_12735793724305513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548870 : Nat.totient 50837476016421357502988548870 = 17429991777058751143881788160 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (726249657377447964328407841, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548870 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_5, prime_fortyThreeAO_7, prime_fortyThreeAO_726249657377447964328407841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548871 : Nat.totient 50837476016421357502988548871 = 50836265571505611381473637744 := by
  rw [← show ((([(41999, 1), (1210444915746121514869129, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548871 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_41999, prime_fortyThreeAO_1210444915746121514869129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548872 : Nat.totient 50837476016421357502988548872 = 16945761415768719479217671040 := by
  rw [← show ((([(2, 3), (3, 2), (401587, 1), (779981, 1), (2254175965482383, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548872 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_3, prime_fortyThreeAO_401587, prime_fortyThreeAO_779981, prime_fortyThreeAO_2254175965482383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548873 : Nat.totient 50837476016421357502988548873 = 50837476016421357502988548872 := by
  rw [← show ((([(50837476016421357502988548873, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548873 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_50837476016421357502988548873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548874 : Nat.totient 50837476016421357502988548874 = 24731745085318657938884819712 := by
  rw [← show ((([(2, 1), (37, 1), (6593037337, 1), (104199761661508873, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548874 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_37, prime_fortyThreeAO_6593037337, prime_fortyThreeAO_104199761661508873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548875 : Nat.totient 50837476016421357502988548875 = 27113308403286067219512204000 := by
  rw [← show ((([(3, 1), (5, 3), (2233607, 1), (60694026617241508171, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548875 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3, prime_fortyThreeAO_5, prime_fortyThreeAO_2233607, prime_fortyThreeAO_60694026617241508171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548876 : Nat.totient 50837476016421357502988548876 = 24080909314763295210292989120 := by
  rw [← show ((([(2, 2), (19, 1), (69289013, 1), (875720611, 1), (11024031407, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548876 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_19, prime_fortyThreeAO_69289013, prime_fortyThreeAO_875720611, prime_fortyThreeAO_11024031407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548877 : Nat.totient 50837476016421357502988548877 = 39455794497144945544824750000 := by
  rw [← show ((([(7, 1), (11, 1), (251, 1), (2630386299809663036321651, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548877 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_7, prime_fortyThreeAO_11, prime_fortyThreeAO_251, prime_fortyThreeAO_2630386299809663036321651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548878 : Nat.totient 50837476016421357502988548878 = 15624075102861125216070720000 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (1621, 1), (1823, 1), (81299501, 1), (2712887686447, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548878 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_3, prime_fortyThreeAO_13, prime_fortyThreeAO_1621, prime_fortyThreeAO_1823, prime_fortyThreeAO_81299501, prime_fortyThreeAO_2712887686447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548879 : Nat.totient 50837476016421357502988548879 = 50456092692818262902314373280 := by
  rw [← show ((([(181, 1), (503, 1), (16072387, 1), (34742177880057719, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548879 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_181, prime_fortyThreeAO_503, prime_fortyThreeAO_16072387, prime_fortyThreeAO_34742177880057719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548880 : Nat.totient 50837476016421357502988548880 = 20334790958519637378141382656 := by
  rw [← show ((([(2, 4), (5, 1), (101957, 1), (16075861309, 1), (387706153997, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548880 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_5, prime_fortyThreeAO_101957, prime_fortyThreeAO_16075861309, prime_fortyThreeAO_387706153997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548881 : Nat.totient 50837476016421357502988548881 = 33891058722509024377833273600 := by
  rw [← show ((([(3, 3), (57329, 1), (43618901, 1), (752958657021607, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548881 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3, prime_fortyThreeAO_57329, prime_fortyThreeAO_43618901, prime_fortyThreeAO_752958657021607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548882 : Nat.totient 50837476016421357502988548882 = 24770615670700636561924176000 := by
  rw [← show ((([(2, 1), (41, 1), (971, 1), (9479, 1), (112341631, 1), (599580707419, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548882 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_41, prime_fortyThreeAO_971, prime_fortyThreeAO_9479, prime_fortyThreeAO_112341631, prime_fortyThreeAO_599580707419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548883 : Nat.totient 50837476016421357502988548883 = 50751746714538690795563609760 := by
  rw [← show ((([(593, 1), (85729301882666707424938531, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548883 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_593, prime_fortyThreeAO_85729301882666707424938531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548884 : Nat.totient 50837476016421357502988548884 = 14410623120039085816865963520 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (127, 1), (5286347743, 1), (901457477071441, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548884 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_3, prime_fortyThreeAO_7, prime_fortyThreeAO_127, prime_fortyThreeAO_5286347743, prime_fortyThreeAO_901457477071441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548885 : Nat.totient 50837476016421357502988548885 = 38277312121741023691835904000 := by
  rw [← show ((([(5, 1), (17, 1), (142733, 1), (842267, 1), (12098971, 1), (411189901, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548885 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_5, prime_fortyThreeAO_17, prime_fortyThreeAO_142733, prime_fortyThreeAO_842267, prime_fortyThreeAO_12098971, prime_fortyThreeAO_411189901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548886 : Nat.totient 50837476016421357502988548886 = 24827604545852314306052656200 := by
  rw [← show ((([(2, 1), (43, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548886 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_43, prime_fortyThreeAO_1222615931, prime_fortyThreeAO_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548887 : Nat.totient 50837476016421357502988548887 = 32308758214635993261706289664 := by
  rw [← show ((([(3, 1), (29, 2), (79, 1), (7273683217, 1), (35065921476683, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548887 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3, prime_fortyThreeAO_29, prime_fortyThreeAO_79, prime_fortyThreeAO_7273683217, prime_fortyThreeAO_35065921476683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548888 : Nat.totient 50837476016421357502988548888 = 23107943643827889774085703600 := by
  rw [← show ((([(2, 3), (11, 2), (52518053735972476759285691, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548888 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_11, prime_fortyThreeAO_52518053735972476759285691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548889 : Nat.totient 50837476016421357502988548889 = 50837461381882414016769974400 := by
  rw [← show ((([(3473801, 1), (14634538943486215100689, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548889 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3473801, prime_fortyThreeAO_14634538943486215100689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548890 : Nat.totient 50837476016421357502988548890 = 13556475723743512542430642656 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (73459, 1), (7689470924282987411419, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548890 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_3, prime_fortyThreeAO_5, prime_fortyThreeAO_73459, prime_fortyThreeAO_7689470924282987411419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548891 : Nat.totient 50837476016421357502988548891 = 40223057929957675765770983424 := by
  rw [← show ((([(7, 1), (13, 1), (2352090737, 1), (237513618760549073, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548891 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_7, prime_fortyThreeAO_13, prime_fortyThreeAO_2352090737, prime_fortyThreeAO_237513618760549073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548892 : Nat.totient 50837476016421357502988548892 = 24313575482593829085226579776 := by
  rw [← show ((([(2, 2), (23, 1), (6905827909, 1), (80016656703522589, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548892 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_23, prime_fortyThreeAO_6905827909, prime_fortyThreeAO_80016656703522589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548893 : Nat.totient 50837476016421357502988548893 = 32110637457213174378637071360 := by
  rw [← show ((([(3, 1), (31, 1), (67, 1), (167, 1), (6779, 1), (12248567, 1), (588381273713, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548893 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3, prime_fortyThreeAO_31, prime_fortyThreeAO_67, prime_fortyThreeAO_167, prime_fortyThreeAO_6779, prime_fortyThreeAO_12248567, prime_fortyThreeAO_588381273713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548894 : Nat.totient 50837476016421357502988548894 = 24877913795267879837682396832 := by
  rw [← show ((([(2, 1), (47, 1), (21492071870237, 1), (25163893746773, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548894 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_47, prime_fortyThreeAO_21492071870237, prime_fortyThreeAO_25163893746773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548895 : Nat.totient 50837476016421357502988548895 = 38529375589951815407987113344 := by
  rw [← show ((([(5, 1), (19, 1), (482117, 1), (1109961537321118874573, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548895 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_5, prime_fortyThreeAO_19, prime_fortyThreeAO_482117, prime_fortyThreeAO_1109961537321118874573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548896 : Nat.totient 50837476016421357502988548896 = 16945691191874542951347507200 := by
  rw [← show ((([(2, 5), (3, 1), (133949, 1), (3615701, 1), (5927477, 1), (184463687, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548896 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_3, prime_fortyThreeAO_133949, prime_fortyThreeAO_3615701, prime_fortyThreeAO_5927477, prime_fortyThreeAO_184463687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548897 : Nat.totient 50837476016421357502988548897 = 50829745885463623933857912000 := by
  rw [← show ((([(6577, 1), (92984711, 1), (83127475778810951, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548897 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_6577, prime_fortyThreeAO_92984711, prime_fortyThreeAO_83127475778810951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548898 : Nat.totient 50837476016421357502988548898 = 21664694718844069572740712960 := by
  rw [← show ((([(2, 1), (7, 2), (197, 1), (1777, 1), (1167364339, 1), (1269398055311, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548898 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_7, prime_fortyThreeAO_197, prime_fortyThreeAO_1777, prime_fortyThreeAO_1167364339, prime_fortyThreeAO_1269398055311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548899 : Nat.totient 50837476016421357502988548899 = 30810591525103853032114272000 := by
  rw [← show ((([(3, 2), (11, 1), (513509858751730883868571201, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548899 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_3, prime_fortyThreeAO_11, prime_fortyThreeAO_513509858751730883868571201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyThreeAO_50837476016421357502988548900 : Nat.totient 50837476016421357502988548900 = 20334984883428951980141961600 := by
  rw [← show ((([(2, 2), (5, 2), (3681781, 1), (138078489775522654669, 1)] : List FactorBlock).map factorBlockValue).prod) = 50837476016421357502988548900 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyThreeAO_2, prime_fortyThreeAO_5, prime_fortyThreeAO_3681781, prime_fortyThreeAO_138078489775522654669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FortyThreeAO : certifiedKill 1 50837476016421357502988548799 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fortyThreeAO_50837476016421357502988548800, phi_fortyThreeAO_50837476016421357502988548801, phi_fortyThreeAO_50837476016421357502988548802,
    phi_fortyThreeAO_50837476016421357502988548803, phi_fortyThreeAO_50837476016421357502988548804, phi_fortyThreeAO_50837476016421357502988548805,
    phi_fortyThreeAO_50837476016421357502988548806, phi_fortyThreeAO_50837476016421357502988548807, phi_fortyThreeAO_50837476016421357502988548808,
    phi_fortyThreeAO_50837476016421357502988548809, phi_fortyThreeAO_50837476016421357502988548810, phi_fortyThreeAO_50837476016421357502988548811,
    phi_fortyThreeAO_50837476016421357502988548812, phi_fortyThreeAO_50837476016421357502988548813, phi_fortyThreeAO_50837476016421357502988548814,
    phi_fortyThreeAO_50837476016421357502988548815, phi_fortyThreeAO_50837476016421357502988548816, phi_fortyThreeAO_50837476016421357502988548817,
    phi_fortyThreeAO_50837476016421357502988548818, phi_fortyThreeAO_50837476016421357502988548819, phi_fortyThreeAO_50837476016421357502988548820,
    phi_fortyThreeAO_50837476016421357502988548821, phi_fortyThreeAO_50837476016421357502988548822, phi_fortyThreeAO_50837476016421357502988548823,
    phi_fortyThreeAO_50837476016421357502988548824, phi_fortyThreeAO_50837476016421357502988548825, phi_fortyThreeAO_50837476016421357502988548826,
    phi_fortyThreeAO_50837476016421357502988548827, phi_fortyThreeAO_50837476016421357502988548828, phi_fortyThreeAO_50837476016421357502988548829,
    phi_fortyThreeAO_50837476016421357502988548830, phi_fortyThreeAO_50837476016421357502988548831, phi_fortyThreeAO_50837476016421357502988548832,
    phi_fortyThreeAO_50837476016421357502988548833, phi_fortyThreeAO_50837476016421357502988548834, phi_fortyThreeAO_50837476016421357502988548835,
    phi_fortyThreeAO_50837476016421357502988548836, phi_fortyThreeAO_50837476016421357502988548837, phi_fortyThreeAO_50837476016421357502988548838,
    phi_fortyThreeAO_50837476016421357502988548839, phi_fortyThreeAO_50837476016421357502988548840, phi_fortyThreeAO_50837476016421357502988548841,
    phi_fortyThreeAO_50837476016421357502988548842, phi_fortyThreeAO_50837476016421357502988548843, phi_fortyThreeAO_50837476016421357502988548844,
    phi_fortyThreeAO_50837476016421357502988548845, phi_fortyThreeAO_50837476016421357502988548846, phi_fortyThreeAO_50837476016421357502988548847,
    phi_fortyThreeAO_50837476016421357502988548848, phi_fortyThreeAO_50837476016421357502988548849, phi_fortyThreeAO_50837476016421357502988548850,
    phi_fortyThreeAO_50837476016421357502988548851, phi_fortyThreeAO_50837476016421357502988548852, phi_fortyThreeAO_50837476016421357502988548853,
    phi_fortyThreeAO_50837476016421357502988548854, phi_fortyThreeAO_50837476016421357502988548855, phi_fortyThreeAO_50837476016421357502988548856,
    phi_fortyThreeAO_50837476016421357502988548857, phi_fortyThreeAO_50837476016421357502988548858, phi_fortyThreeAO_50837476016421357502988548859,
    phi_fortyThreeAO_50837476016421357502988548860, phi_fortyThreeAO_50837476016421357502988548861, phi_fortyThreeAO_50837476016421357502988548862,
    phi_fortyThreeAO_50837476016421357502988548863, phi_fortyThreeAO_50837476016421357502988548864, phi_fortyThreeAO_50837476016421357502988548865,
    phi_fortyThreeAO_50837476016421357502988548866, phi_fortyThreeAO_50837476016421357502988548867, phi_fortyThreeAO_50837476016421357502988548868,
    phi_fortyThreeAO_50837476016421357502988548869, phi_fortyThreeAO_50837476016421357502988548870, phi_fortyThreeAO_50837476016421357502988548871,
    phi_fortyThreeAO_50837476016421357502988548872, phi_fortyThreeAO_50837476016421357502988548873, phi_fortyThreeAO_50837476016421357502988548874,
    phi_fortyThreeAO_50837476016421357502988548875, phi_fortyThreeAO_50837476016421357502988548876, phi_fortyThreeAO_50837476016421357502988548877,
    phi_fortyThreeAO_50837476016421357502988548878, phi_fortyThreeAO_50837476016421357502988548879, phi_fortyThreeAO_50837476016421357502988548880,
    phi_fortyThreeAO_50837476016421357502988548881, phi_fortyThreeAO_50837476016421357502988548882, phi_fortyThreeAO_50837476016421357502988548883,
    phi_fortyThreeAO_50837476016421357502988548884, phi_fortyThreeAO_50837476016421357502988548885, phi_fortyThreeAO_50837476016421357502988548886,
    phi_fortyThreeAO_50837476016421357502988548887, phi_fortyThreeAO_50837476016421357502988548888, phi_fortyThreeAO_50837476016421357502988548889,
    phi_fortyThreeAO_50837476016421357502988548890, phi_fortyThreeAO_50837476016421357502988548891, phi_fortyThreeAO_50837476016421357502988548892,
    phi_fortyThreeAO_50837476016421357502988548893, phi_fortyThreeAO_50837476016421357502988548894, phi_fortyThreeAO_50837476016421357502988548895,
    phi_fortyThreeAO_50837476016421357502988548896, phi_fortyThreeAO_50837476016421357502988548897, phi_fortyThreeAO_50837476016421357502988548898,
    phi_fortyThreeAO_50837476016421357502988548899, phi_fortyThreeAO_50837476016421357502988548900]

end TotientTailPeriodKiller
end Erdos249257
