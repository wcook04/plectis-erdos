import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fortyFourAPFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fortyFourAPFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fortyFourAPFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fortyFourAPFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fortyFourAPFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fortyFourAPFastPow a n * fortyFourAPFastPow a n * a
        else fortyFourAPFastPow a n * fortyFourAPFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fortyFourAP_2 : Nat.Prime 2 := by norm_num
private theorem prime_fortyFourAP_3 : Nat.Prime 3 := by norm_num
private theorem prime_fortyFourAP_5 : Nat.Prime 5 := by norm_num
private theorem prime_fortyFourAP_7 : Nat.Prime 7 := by norm_num
private theorem prime_fortyFourAP_11 : Nat.Prime 11 := by norm_num
private theorem prime_fortyFourAP_13 : Nat.Prime 13 := by norm_num
private theorem prime_fortyFourAP_17 : Nat.Prime 17 := by norm_num
private theorem prime_fortyFourAP_19 : Nat.Prime 19 := by norm_num
private theorem prime_fortyFourAP_23 : Nat.Prime 23 := by norm_num
private theorem prime_fortyFourAP_29 : Nat.Prime 29 := by norm_num
private theorem prime_fortyFourAP_31 : Nat.Prime 31 := by norm_num
private theorem prime_fortyFourAP_37 : Nat.Prime 37 := by norm_num
private theorem prime_fortyFourAP_41 : Nat.Prime 41 := by norm_num
private theorem prime_fortyFourAP_43 : Nat.Prime 43 := by norm_num
private theorem prime_fortyFourAP_47 : Nat.Prime 47 := by norm_num
private theorem prime_fortyFourAP_53 : Nat.Prime 53 := by norm_num
private theorem prime_fortyFourAP_59 : Nat.Prime 59 := by norm_num
private theorem prime_fortyFourAP_61 : Nat.Prime 61 := by norm_num
private theorem prime_fortyFourAP_67 : Nat.Prime 67 := by norm_num
private theorem prime_fortyFourAP_71 : Nat.Prime 71 := by norm_num
private theorem prime_fortyFourAP_73 : Nat.Prime 73 := by norm_num
private theorem prime_fortyFourAP_79 : Nat.Prime 79 := by norm_num
private theorem prime_fortyFourAP_83 : Nat.Prime 83 := by norm_num
private theorem prime_fortyFourAP_89 : Nat.Prime 89 := by norm_num
private theorem prime_fortyFourAP_97 : Nat.Prime 97 := by norm_num
private theorem prime_fortyFourAP_101 : Nat.Prime 101 := by norm_num
private theorem prime_fortyFourAP_103 : Nat.Prime 103 := by norm_num
private theorem prime_fortyFourAP_107 : Nat.Prime 107 := by norm_num
private theorem prime_fortyFourAP_109 : Nat.Prime 109 := by norm_num
private theorem prime_fortyFourAP_113 : Nat.Prime 113 := by norm_num
private theorem prime_fortyFourAP_127 : Nat.Prime 127 := by norm_num
private theorem prime_fortyFourAP_131 : Nat.Prime 131 := by norm_num
private theorem prime_fortyFourAP_137 : Nat.Prime 137 := by norm_num
private theorem prime_fortyFourAP_139 : Nat.Prime 139 := by norm_num
private theorem prime_fortyFourAP_151 : Nat.Prime 151 := by norm_num
private theorem prime_fortyFourAP_157 : Nat.Prime 157 := by norm_num
private theorem prime_fortyFourAP_163 : Nat.Prime 163 := by norm_num
private theorem prime_fortyFourAP_167 : Nat.Prime 167 := by norm_num
private theorem prime_fortyFourAP_173 : Nat.Prime 173 := by norm_num
private theorem prime_fortyFourAP_179 : Nat.Prime 179 := by norm_num
private theorem prime_fortyFourAP_181 : Nat.Prime 181 := by norm_num
private theorem prime_fortyFourAP_191 : Nat.Prime 191 := by norm_num
private theorem prime_fortyFourAP_199 : Nat.Prime 199 := by norm_num
private theorem prime_fortyFourAP_211 : Nat.Prime 211 := by norm_num
private theorem prime_fortyFourAP_223 : Nat.Prime 223 := by norm_num
private theorem prime_fortyFourAP_229 : Nat.Prime 229 := by norm_num
private theorem prime_fortyFourAP_233 : Nat.Prime 233 := by norm_num
private theorem prime_fortyFourAP_239 : Nat.Prime 239 := by norm_num
private theorem prime_fortyFourAP_241 : Nat.Prime 241 := by norm_num
private theorem prime_fortyFourAP_251 : Nat.Prime 251 := by norm_num
private theorem prime_fortyFourAP_257 : Nat.Prime 257 := by norm_num
private theorem prime_fortyFourAP_263 : Nat.Prime 263 := by norm_num
private theorem prime_fortyFourAP_269 : Nat.Prime 269 := by norm_num
private theorem prime_fortyFourAP_271 : Nat.Prime 271 := by norm_num
private theorem prime_fortyFourAP_277 : Nat.Prime 277 := by norm_num
private theorem prime_fortyFourAP_293 : Nat.Prime 293 := by norm_num
private theorem prime_fortyFourAP_307 : Nat.Prime 307 := by norm_num
private theorem prime_fortyFourAP_313 : Nat.Prime 313 := by norm_num
private theorem prime_fortyFourAP_331 : Nat.Prime 331 := by norm_num
private theorem prime_fortyFourAP_337 : Nat.Prime 337 := by norm_num
private theorem prime_fortyFourAP_347 : Nat.Prime 347 := by norm_num
private theorem prime_fortyFourAP_349 : Nat.Prime 349 := by norm_num
private theorem prime_fortyFourAP_359 : Nat.Prime 359 := by norm_num
private theorem prime_fortyFourAP_367 : Nat.Prime 367 := by norm_num
private theorem prime_fortyFourAP_373 : Nat.Prime 373 := by norm_num
private theorem prime_fortyFourAP_379 : Nat.Prime 379 := by norm_num
private theorem prime_fortyFourAP_383 : Nat.Prime 383 := by norm_num
private theorem prime_fortyFourAP_397 : Nat.Prime 397 := by norm_num
private theorem prime_fortyFourAP_401 : Nat.Prime 401 := by norm_num
private theorem prime_fortyFourAP_419 : Nat.Prime 419 := by norm_num
private theorem prime_fortyFourAP_421 : Nat.Prime 421 := by norm_num
private theorem prime_fortyFourAP_439 : Nat.Prime 439 := by norm_num
private theorem prime_fortyFourAP_443 : Nat.Prime 443 := by norm_num
private theorem prime_fortyFourAP_449 : Nat.Prime 449 := by norm_num
private theorem prime_fortyFourAP_479 : Nat.Prime 479 := by norm_num
private theorem prime_fortyFourAP_499 : Nat.Prime 499 := by norm_num
private theorem prime_fortyFourAP_557 : Nat.Prime 557 := by norm_num
private theorem prime_fortyFourAP_563 : Nat.Prime 563 := by norm_num
private theorem prime_fortyFourAP_571 : Nat.Prime 571 := by norm_num
private theorem prime_fortyFourAP_593 : Nat.Prime 593 := by norm_num
private theorem prime_fortyFourAP_599 : Nat.Prime 599 := by norm_num
private theorem prime_fortyFourAP_617 : Nat.Prime 617 := by norm_num
private theorem prime_fortyFourAP_631 : Nat.Prime 631 := by norm_num
private theorem prime_fortyFourAP_641 : Nat.Prime 641 := by norm_num
private theorem prime_fortyFourAP_643 : Nat.Prime 643 := by norm_num
private theorem prime_fortyFourAP_647 : Nat.Prime 647 := by norm_num
private theorem prime_fortyFourAP_659 : Nat.Prime 659 := by norm_num
private theorem prime_fortyFourAP_661 : Nat.Prime 661 := by norm_num
private theorem prime_fortyFourAP_727 : Nat.Prime 727 := by norm_num
private theorem prime_fortyFourAP_757 : Nat.Prime 757 := by norm_num
private theorem prime_fortyFourAP_761 : Nat.Prime 761 := by norm_num
private theorem prime_fortyFourAP_769 : Nat.Prime 769 := by norm_num
private theorem prime_fortyFourAP_773 : Nat.Prime 773 := by norm_num
private theorem prime_fortyFourAP_787 : Nat.Prime 787 := by norm_num
private theorem prime_fortyFourAP_809 : Nat.Prime 809 := by norm_num
private theorem prime_fortyFourAP_811 : Nat.Prime 811 := by norm_num
private theorem prime_fortyFourAP_821 : Nat.Prime 821 := by norm_num
private theorem prime_fortyFourAP_827 : Nat.Prime 827 := by norm_num
private theorem prime_fortyFourAP_839 : Nat.Prime 839 := by norm_num
private theorem prime_fortyFourAP_853 : Nat.Prime 853 := by norm_num
private theorem prime_fortyFourAP_857 : Nat.Prime 857 := by norm_num
private theorem prime_fortyFourAP_883 : Nat.Prime 883 := by norm_num
private theorem prime_fortyFourAP_911 : Nat.Prime 911 := by norm_num
private theorem prime_fortyFourAP_947 : Nat.Prime 947 := by norm_num
private theorem prime_fortyFourAP_967 : Nat.Prime 967 := by norm_num
private theorem prime_fortyFourAP_977 : Nat.Prime 977 := by norm_num
private theorem prime_fortyFourAP_997 : Nat.Prime 997 := by norm_num
private theorem prime_fortyFourAP_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_fortyFourAP_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_fortyFourAP_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_fortyFourAP_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_fortyFourAP_1039 : Nat.Prime 1039 := by norm_num
private theorem prime_fortyFourAP_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_fortyFourAP_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_fortyFourAP_1129 : Nat.Prime 1129 := by norm_num
private theorem prime_fortyFourAP_1181 : Nat.Prime 1181 := by norm_num
private theorem prime_fortyFourAP_1201 : Nat.Prime 1201 := by norm_num
private theorem prime_fortyFourAP_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_fortyFourAP_1217 : Nat.Prime 1217 := by norm_num
private theorem prime_fortyFourAP_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_fortyFourAP_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_fortyFourAP_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_fortyFourAP_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_fortyFourAP_1291 : Nat.Prime 1291 := by norm_num
private theorem prime_fortyFourAP_1307 : Nat.Prime 1307 := by norm_num
private theorem prime_fortyFourAP_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_fortyFourAP_1381 : Nat.Prime 1381 := by norm_num
private theorem prime_fortyFourAP_1427 : Nat.Prime 1427 := by norm_num
private theorem prime_fortyFourAP_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_fortyFourAP_1487 : Nat.Prime 1487 := by norm_num
private theorem prime_fortyFourAP_1553 : Nat.Prime 1553 := by norm_num
private theorem prime_fortyFourAP_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_fortyFourAP_1627 : Nat.Prime 1627 := by norm_num
private theorem prime_fortyFourAP_1637 : Nat.Prime 1637 := by norm_num
private theorem prime_fortyFourAP_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_fortyFourAP_1667 : Nat.Prime 1667 := by norm_num
private theorem prime_fortyFourAP_1697 : Nat.Prime 1697 := by norm_num
private theorem prime_fortyFourAP_1709 : Nat.Prime 1709 := by norm_num
private theorem prime_fortyFourAP_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_fortyFourAP_1753 : Nat.Prime 1753 := by norm_num
private theorem prime_fortyFourAP_1787 : Nat.Prime 1787 := by norm_num
private theorem prime_fortyFourAP_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_fortyFourAP_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_fortyFourAP_2081 : Nat.Prime 2081 := by norm_num
private theorem prime_fortyFourAP_2113 : Nat.Prime 2113 := by norm_num
private theorem prime_fortyFourAP_2137 : Nat.Prime 2137 := by norm_num
private theorem prime_fortyFourAP_2203 : Nat.Prime 2203 := by norm_num
private theorem prime_fortyFourAP_2311 : Nat.Prime 2311 := by norm_num
private theorem prime_fortyFourAP_2339 : Nat.Prime 2339 := by norm_num
private theorem prime_fortyFourAP_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_fortyFourAP_2593 : Nat.Prime 2593 := by norm_num
private theorem prime_fortyFourAP_2741 : Nat.Prime 2741 := by norm_num
private theorem prime_fortyFourAP_2753 : Nat.Prime 2753 := by norm_num
private theorem prime_fortyFourAP_2833 : Nat.Prime 2833 := by norm_num
private theorem prime_fortyFourAP_2887 : Nat.Prime 2887 := by norm_num
private theorem prime_fortyFourAP_2969 : Nat.Prime 2969 := by norm_num
private theorem prime_fortyFourAP_3011 : Nat.Prime 3011 := by norm_num
private theorem prime_fortyFourAP_3061 : Nat.Prime 3061 := by norm_num
private theorem prime_fortyFourAP_3083 : Nat.Prime 3083 := by norm_num
private theorem prime_fortyFourAP_3203 : Nat.Prime 3203 := by norm_num
private theorem prime_fortyFourAP_3221 : Nat.Prime 3221 := by norm_num
private theorem prime_fortyFourAP_3251 : Nat.Prime 3251 := by norm_num
private theorem prime_fortyFourAP_3329 : Nat.Prime 3329 := by norm_num
private theorem prime_fortyFourAP_3343 : Nat.Prime 3343 := by norm_num
private theorem prime_fortyFourAP_3607 : Nat.Prime 3607 := by norm_num
private theorem prime_fortyFourAP_3673 : Nat.Prime 3673 := by norm_num
private theorem prime_fortyFourAP_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_fortyFourAP_3769 : Nat.Prime 3769 := by norm_num
private theorem prime_fortyFourAP_3793 : Nat.Prime 3793 := by norm_num
private theorem prime_fortyFourAP_3907 : Nat.Prime 3907 := by norm_num
private theorem prime_fortyFourAP_4051 : Nat.Prime 4051 := by norm_num
private theorem prime_fortyFourAP_4211 : Nat.Prime 4211 := by norm_num
private theorem prime_fortyFourAP_4273 : Nat.Prime 4273 := by norm_num
private theorem prime_fortyFourAP_4339 : Nat.Prime 4339 := by norm_num
private theorem prime_fortyFourAP_4493 : Nat.Prime 4493 := by norm_num
private theorem prime_fortyFourAP_4691 : Nat.Prime 4691 := by norm_num
private theorem prime_fortyFourAP_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fortyFourAP_5051 : Nat.Prime 5051 := by norm_num
private theorem prime_fortyFourAP_5441 : Nat.Prime 5441 := by norm_num
private theorem prime_fortyFourAP_5639 : Nat.Prime 5639 := by norm_num
private theorem prime_fortyFourAP_5843 : Nat.Prime 5843 := by norm_num
private theorem prime_fortyFourAP_5857 : Nat.Prime 5857 := by norm_num
private theorem prime_fortyFourAP_5897 : Nat.Prime 5897 := by norm_num
private theorem prime_fortyFourAP_5927 : Nat.Prime 5927 := by norm_num
private theorem prime_fortyFourAP_6217 : Nat.Prime 6217 := by norm_num
private theorem prime_fortyFourAP_6269 : Nat.Prime 6269 := by norm_num
private theorem prime_fortyFourAP_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_fortyFourAP_6379 : Nat.Prime 6379 := by norm_num
private theorem prime_fortyFourAP_6529 : Nat.Prime 6529 := by norm_num
private theorem prime_fortyFourAP_6599 : Nat.Prime 6599 := by norm_num
private theorem prime_fortyFourAP_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_fortyFourAP_7019 : Nat.Prime 7019 := by norm_num
private theorem prime_fortyFourAP_7187 : Nat.Prime 7187 := by norm_num
private theorem prime_fortyFourAP_7673 : Nat.Prime 7673 := by norm_num
private theorem prime_fortyFourAP_7759 : Nat.Prime 7759 := by norm_num
private theorem prime_fortyFourAP_7841 : Nat.Prime 7841 := by norm_num
private theorem prime_fortyFourAP_8669 : Nat.Prime 8669 := by norm_num
private theorem prime_fortyFourAP_8933 : Nat.Prime 8933 := by norm_num
private theorem prime_fortyFourAP_8971 : Nat.Prime 8971 := by norm_num
private theorem prime_fortyFourAP_9103 : Nat.Prime 9103 := by norm_num
private theorem prime_fortyFourAP_9241 : Nat.Prime 9241 := by norm_num
private theorem prime_fortyFourAP_9257 : Nat.Prime 9257 := by norm_num
private theorem prime_fortyFourAP_9431 : Nat.Prime 9431 := by norm_num
private theorem prime_fortyFourAP_9511 : Nat.Prime 9511 := by norm_num
private theorem prime_fortyFourAP_10691 : Nat.Prime 10691 := by norm_num
private theorem prime_fortyFourAP_10903 : Nat.Prime 10903 := by norm_num
private theorem prime_fortyFourAP_11069 : Nat.Prime 11069 := by norm_num
private theorem prime_fortyFourAP_11827 : Nat.Prime 11827 := by norm_num
private theorem prime_fortyFourAP_11933 : Nat.Prime 11933 := by norm_num
private theorem prime_fortyFourAP_12721 : Nat.Prime 12721 := by norm_num
private theorem prime_fortyFourAP_12919 : Nat.Prime 12919 := by norm_num
private theorem prime_fortyFourAP_13711 : Nat.Prime 13711 := by norm_num
private theorem prime_fortyFourAP_14423 : Nat.Prime 14423 := by norm_num
private theorem prime_fortyFourAP_14813 : Nat.Prime 14813 := by norm_num
private theorem prime_fortyFourAP_16087 : Nat.Prime 16087 := by norm_num
private theorem prime_fortyFourAP_16253 : Nat.Prime 16253 := by norm_num
private theorem prime_fortyFourAP_16349 : Nat.Prime 16349 := by norm_num
private theorem prime_fortyFourAP_17599 : Nat.Prime 17599 := by norm_num
private theorem prime_fortyFourAP_17707 : Nat.Prime 17707 := by norm_num
private theorem prime_fortyFourAP_17749 : Nat.Prime 17749 := by norm_num
private theorem prime_fortyFourAP_18077 : Nat.Prime 18077 := by norm_num
private theorem prime_fortyFourAP_18217 : Nat.Prime 18217 := by norm_num
private theorem prime_fortyFourAP_18503 : Nat.Prime 18503 := by norm_num
private theorem prime_fortyFourAP_18539 : Nat.Prime 18539 := by norm_num
private theorem prime_fortyFourAP_18679 : Nat.Prime 18679 := by norm_num
private theorem prime_fortyFourAP_18979 : Nat.Prime 18979 := by norm_num
private theorem prime_fortyFourAP_19541 : Nat.Prime 19541 := by norm_num
private theorem prime_fortyFourAP_19841 : Nat.Prime 19841 := by norm_num
private theorem prime_fortyFourAP_19867 : Nat.Prime 19867 := by norm_num
private theorem prime_fortyFourAP_22193 : Nat.Prime 22193 := by norm_num
private theorem prime_fortyFourAP_22511 : Nat.Prime 22511 := by norm_num
private theorem prime_fortyFourAP_23599 : Nat.Prime 23599 := by norm_num
private theorem prime_fortyFourAP_24919 : Nat.Prime 24919 := by norm_num
private theorem prime_fortyFourAP_25309 : Nat.Prime 25309 := by norm_num
private theorem prime_fortyFourAP_25439 : Nat.Prime 25439 := by norm_num
private theorem prime_fortyFourAP_26501 : Nat.Prime 26501 := by norm_num
private theorem prime_fortyFourAP_26833 : Nat.Prime 26833 := by norm_num
private theorem prime_fortyFourAP_27077 : Nat.Prime 27077 := by norm_num
private theorem prime_fortyFourAP_27361 : Nat.Prime 27361 := by norm_num
private theorem prime_fortyFourAP_28687 : Nat.Prime 28687 := by norm_num
private theorem prime_fortyFourAP_29873 : Nat.Prime 29873 := by norm_num
private theorem prime_fortyFourAP_31159 : Nat.Prime 31159 := by norm_num
private theorem prime_fortyFourAP_31873 : Nat.Prime 31873 := by norm_num
private theorem prime_fortyFourAP_32531 : Nat.Prime 32531 := by norm_num
private theorem prime_fortyFourAP_32843 : Nat.Prime 32843 := by norm_num
private theorem prime_fortyFourAP_32869 : Nat.Prime 32869 := by norm_num
private theorem prime_fortyFourAP_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_fortyFourAP_35569 : Nat.Prime 35569 := by norm_num
private theorem prime_fortyFourAP_35797 : Nat.Prime 35797 := by norm_num
private theorem prime_fortyFourAP_35911 : Nat.Prime 35911 := by norm_num
private theorem prime_fortyFourAP_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_fortyFourAP_37799 : Nat.Prime 37799 := by norm_num
private theorem prime_fortyFourAP_37889 : Nat.Prime 37889 := by norm_num
private theorem prime_fortyFourAP_37967 : Nat.Prime 37967 := by norm_num
private theorem prime_fortyFourAP_38047 : Nat.Prime 38047 := by norm_num
private theorem prime_fortyFourAP_39113 : Nat.Prime 39113 := by norm_num
private theorem prime_fortyFourAP_47659 : Nat.Prime 47659 := by norm_num
private theorem prime_fortyFourAP_50411 : Nat.Prime 50411 := by norm_num
private theorem prime_fortyFourAP_50821 : Nat.Prime 50821 := by norm_num
private theorem prime_fortyFourAP_51419 : Nat.Prime 51419 := by norm_num
private theorem prime_fortyFourAP_51511 : Nat.Prime 51511 := by norm_num
private theorem prime_fortyFourAP_51593 : Nat.Prime 51593 := by norm_num
private theorem prime_fortyFourAP_52379 : Nat.Prime 52379 := by norm_num
private theorem prime_fortyFourAP_53269 : Nat.Prime 53269 := by norm_num
private theorem prime_fortyFourAP_54779 : Nat.Prime 54779 := by norm_num
private theorem prime_fortyFourAP_55639 : Nat.Prime 55639 := by norm_num
private theorem prime_fortyFourAP_58199 : Nat.Prime 58199 := by norm_num
private theorem prime_fortyFourAP_61379 : Nat.Prime 61379 := by norm_num
private theorem prime_fortyFourAP_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_fortyFourAP_66751 : Nat.Prime 66751 := by norm_num
private theorem prime_fortyFourAP_67121 : Nat.Prime 67121 := by norm_num
private theorem prime_fortyFourAP_67399 : Nat.Prime 67399 := by norm_num
private theorem prime_fortyFourAP_67901 : Nat.Prime 67901 := by norm_num
private theorem prime_fortyFourAP_71429 : Nat.Prime 71429 := by norm_num
private theorem prime_fortyFourAP_72073 : Nat.Prime 72073 := by norm_num
private theorem prime_fortyFourAP_73141 : Nat.Prime 73141 := by norm_num
private theorem prime_fortyFourAP_74687 : Nat.Prime 74687 := by norm_num
private theorem prime_fortyFourAP_77527 : Nat.Prime 77527 := by norm_num
private theorem prime_fortyFourAP_84349 : Nat.Prime 84349 := by norm_num
private theorem prime_fortyFourAP_89759 : Nat.Prime 89759 := by norm_num
private theorem prime_fortyFourAP_104053 : Nat.Prime 104053 := by norm_num
private theorem prime_fortyFourAP_123923 : Nat.Prime 123923 := by norm_num
private theorem prime_fortyFourAP_130021 : Nat.Prime 130021 := by norm_num
private theorem prime_fortyFourAP_142237 : Nat.Prime 142237 := by norm_num
private theorem prime_fortyFourAP_154807 : Nat.Prime 154807 := by norm_num
private theorem prime_fortyFourAP_158761 : Nat.Prime 158761 := by norm_num
private theorem prime_fortyFourAP_159671 : Nat.Prime 159671 := by norm_num
private theorem prime_fortyFourAP_163987 : Nat.Prime 163987 := by norm_num
private theorem prime_fortyFourAP_174157 : Nat.Prime 174157 := by norm_num
private theorem prime_fortyFourAP_182279 : Nat.Prime 182279 := by norm_num
private theorem prime_fortyFourAP_189529 : Nat.Prime 189529 := by norm_num
private theorem prime_fortyFourAP_198251 : Nat.Prime 198251 := by norm_num
private theorem prime_fortyFourAP_205111 : Nat.Prime 205111 := by norm_num
private theorem prime_fortyFourAP_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_fortyFourAP_221489 : Nat.Prime 221489 := by norm_num
private theorem prime_fortyFourAP_222419 : Nat.Prime 222419 := by norm_num
private theorem prime_fortyFourAP_246223 : Nat.Prime 246223 := by norm_num
private theorem prime_fortyFourAP_272887 : Nat.Prime 272887 := by norm_num
private theorem prime_fortyFourAP_282977 : Nat.Prime 282977 := by norm_num
private theorem prime_fortyFourAP_288293 : Nat.Prime 288293 := by norm_num
private theorem prime_fortyFourAP_294953 : Nat.Prime 294953 := by norm_num
private theorem prime_fortyFourAP_299969 : Nat.Prime 299969 := by norm_num
private theorem prime_fortyFourAP_320027 : Nat.Prime 320027 := by norm_num
private theorem prime_fortyFourAP_349529 : Nat.Prime 349529 := by norm_num
private theorem prime_fortyFourAP_358993 : Nat.Prime 358993 := by norm_num
private theorem prime_fortyFourAP_373297 : Nat.Prime 373297 := by norm_num
private theorem prime_fortyFourAP_382747 : Nat.Prime 382747 := by norm_num
private theorem prime_fortyFourAP_384973 : Nat.Prime 384973 := by norm_num
private theorem prime_fortyFourAP_385327 : Nat.Prime 385327 := by norm_num
private theorem prime_fortyFourAP_396619 : Nat.Prime 396619 := by norm_num
private theorem prime_fortyFourAP_450581 : Nat.Prime 450581 := by norm_num
private theorem prime_fortyFourAP_512047 : Nat.Prime 512047 := by norm_num
private theorem prime_fortyFourAP_514793 : Nat.Prime 514793 := by norm_num
private theorem prime_fortyFourAP_558863 : Nat.Prime 558863 := by norm_num
private theorem prime_fortyFourAP_565589 : Nat.Prime 565589 := by norm_num
private theorem prime_fortyFourAP_631361 : Nat.Prime 631361 := by norm_num
private theorem prime_fortyFourAP_635363 : Nat.Prime 635363 := by norm_num
private theorem prime_fortyFourAP_737251 : Nat.Prime 737251 := by norm_num
private theorem prime_fortyFourAP_760321 : Nat.Prime 760321 := by norm_num
private theorem prime_fortyFourAP_776813 : Nat.Prime 776813 := by norm_num
private theorem prime_fortyFourAP_781951 : Nat.Prime 781951 := by norm_num
private theorem prime_fortyFourAP_794341 : Nat.Prime 794341 := by norm_num
private theorem prime_fortyFourAP_796447 : Nat.Prime 796447 := by norm_num
private theorem prime_fortyFourAP_810913 : Nat.Prime 810913 := by norm_num
private theorem prime_fortyFourAP_814829 : Nat.Prime 814829 := by norm_num
private theorem prime_fortyFourAP_834527 : Nat.Prime 834527 := by norm_num
private theorem prime_fortyFourAP_895529 : Nat.Prime 895529 := by norm_num
private theorem prime_fortyFourAP_925081 : Nat.Prime 925081 := by norm_num
private theorem prime_fortyFourAP_940573 : Nat.Prime 940573 := by norm_num
private theorem prime_fortyFourAP_1127981 : Nat.Prime 1127981 := by norm_num
private theorem prime_fortyFourAP_1179991 : Nat.Prime 1179991 := by norm_num
private theorem prime_fortyFourAP_1231171 : Nat.Prime 1231171 := by norm_num
private theorem prime_fortyFourAP_1279601 : Nat.Prime 1279601 := by norm_num
private theorem prime_fortyFourAP_1470233 : Nat.Prime 1470233 := by norm_num
private theorem prime_fortyFourAP_1558243 : Nat.Prime 1558243 := by norm_num
private theorem prime_fortyFourAP_1719337 : Nat.Prime 1719337 := by norm_num
private theorem prime_fortyFourAP_1883407 : Nat.Prime 1883407 := by norm_num
private theorem prime_fortyFourAP_1899647 : Nat.Prime 1899647 := by norm_num
private theorem prime_fortyFourAP_1916021 : Nat.Prime 1916021 := by norm_num
private theorem prime_fortyFourAP_1985257 : Nat.Prime 1985257 := by norm_num
private theorem prime_fortyFourAP_2029241 : Nat.Prime 2029241 := by norm_num
private theorem prime_fortyFourAP_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_fortyFourAP_2502833 : Nat.Prime 2502833 := by norm_num
private theorem prime_fortyFourAP_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_fortyFourAP_2719511 : Nat.Prime 2719511 := by norm_num
private theorem prime_fortyFourAP_3072847 : Nat.Prime 3072847 := by norm_num
private theorem prime_fortyFourAP_3086791 : Nat.Prime 3086791 := by norm_num
private theorem prime_fortyFourAP_3446959 : Nat.Prime 3446959 := by norm_num
private theorem prime_fortyFourAP_3707213 : Nat.Prime 3707213 := by norm_num
private theorem prime_fortyFourAP_3715343 : Nat.Prime 3715343 := by norm_num
private theorem prime_fortyFourAP_4033241 : Nat.Prime 4033241 := by norm_num
private theorem prime_fortyFourAP_4237733 : Nat.Prime 4237733 := by norm_num
private theorem prime_fortyFourAP_4331581 : Nat.Prime 4331581 := by norm_num
private theorem prime_fortyFourAP_4885691 : Nat.Prime 4885691 := by norm_num
private theorem prime_fortyFourAP_4917533 : Nat.Prime 4917533 := by norm_num
private theorem prime_fortyFourAP_4938853 : Nat.Prime 4938853 := by norm_num
private theorem prime_fortyFourAP_5049487 : Nat.Prime 5049487 := by norm_num
private theorem prime_fortyFourAP_5225593 : Nat.Prime 5225593 := by norm_num
private theorem prime_fortyFourAP_5339791 : Nat.Prime 5339791 := by norm_num
private theorem prime_fortyFourAP_5426387 : Nat.Prime 5426387 := by norm_num
private theorem prime_fortyFourAP_5905507 : Nat.Prime 5905507 := by norm_num
private theorem prime_fortyFourAP_6283919 : Nat.Prime 6283919 := by norm_num
private theorem prime_fortyFourAP_6372167 : Nat.Prime 6372167 := by norm_num
private theorem prime_fortyFourAP_6672769 : Nat.Prime 6672769 := by norm_num
private theorem prime_fortyFourAP_6785893 : Nat.Prime 6785893 := by norm_num
private theorem prime_fortyFourAP_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_fortyFourAP_7220867 : Nat.Prime 7220867 := by norm_num
private theorem prime_fortyFourAP_8537549 : Nat.Prime 8537549 := by norm_num
private theorem prime_fortyFourAP_8712169 : Nat.Prime 8712169 := by norm_num
private theorem prime_fortyFourAP_8917991 : Nat.Prime 8917991 := by norm_num
private theorem prime_fortyFourAP_9392503 : Nat.Prime 9392503 := by norm_num
private theorem prime_fortyFourAP_10269137 : Nat.Prime 10269137 := by norm_num
private theorem prime_fortyFourAP_10459727 : Nat.Prime 10459727 := by norm_num
private theorem prime_fortyFourAP_10692109 : Nat.Prime 10692109 := by norm_num
private theorem prime_fortyFourAP_11068193 : Nat.Prime 11068193 := by norm_num
private theorem prime_fortyFourAP_11218483 : Nat.Prime 11218483 := by norm_num
private theorem prime_fortyFourAP_11503777 : Nat.Prime 11503777 := by norm_num
private theorem prime_fortyFourAP_11540831 : Nat.Prime 11540831 := by norm_num
private theorem prime_fortyFourAP_12705349 : Nat.Prime 12705349 := by norm_num
private theorem prime_fortyFourAP_13180789 : Nat.Prime 13180789 := by norm_num
private theorem prime_fortyFourAP_13190663 : Nat.Prime 13190663 := by norm_num
private theorem prime_fortyFourAP_13211603 : Nat.Prime 13211603 := by norm_num
private theorem prime_fortyFourAP_14681717 : Nat.Prime 14681717 := by norm_num
private theorem prime_fortyFourAP_15170513 : Nat.Prime 15170513 := by norm_num
private theorem prime_fortyFourAP_17570123 : Nat.Prime 17570123 := by norm_num
private theorem prime_fortyFourAP_18046883 : Nat.Prime 18046883 := by norm_num
private theorem prime_fortyFourAP_18678061 : Nat.Prime 18678061 := by norm_num
private theorem prime_fortyFourAP_19804481 : Nat.Prime 19804481 := by norm_num
private theorem prime_fortyFourAP_20015173 : Nat.Prime 20015173 := by norm_num
private theorem prime_fortyFourAP_21160721 : Nat.Prime 21160721 := by norm_num
private theorem prime_fortyFourAP_21773621 : Nat.Prime 21773621 := by norm_num
private theorem prime_fortyFourAP_22140787 : Nat.Prime 22140787 := by norm_num
private theorem prime_fortyFourAP_22748147 : Nat.Prime 22748147 := by norm_num
private theorem prime_fortyFourAP_22915793 : Nat.Prime 22915793 := by norm_num
private theorem prime_fortyFourAP_23278769 : Nat.Prime 23278769 := by norm_num
private theorem prime_fortyFourAP_24507097 : Nat.Prime 24507097 := by norm_num
private theorem prime_fortyFourAP_25824109 : Nat.Prime 25824109 := by norm_num
private theorem prime_fortyFourAP_26498761 : Nat.Prime 26498761 := by norm_num
private theorem prime_fortyFourAP_27214919 : Nat.Prime 27214919 := by norm_num
private theorem prime_fortyFourAP_27770209 : Nat.Prime 27770209 := by norm_num
private theorem prime_fortyFourAP_28231919 : Nat.Prime 28231919 := by norm_num
private theorem prime_fortyFourAP_28617707 : Nat.Prime 28617707 := by norm_num
private theorem prime_fortyFourAP_29602789 : Nat.Prime 29602789 := by norm_num
private theorem prime_fortyFourAP_29796761 : Nat.Prime 29796761 := by norm_num

private theorem prime_fortyFourAP_32522953 : Nat.Prime 32522953 := by
  apply lucas_primality 32522953 (5 : ZMod 32522953)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (17599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (17599, 1)] : List FactorBlock).map factorBlockValue).prod) = 32522953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_17599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 32522953) ^ 16261476 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 32522953) ^ 10840984 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 32522953) ^ 4646136 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 32522953) ^ 2956632 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 32522953) ^ 1848 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_32804257 : Nat.Prime 32804257 := by
  apply lucas_primality 32804257 (5 : ZMod 32804257)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (23, 1), (83, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (23, 1), (83, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) = 32804257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_23
      · exact prime_fortyFourAP_83
      · exact prime_fortyFourAP_179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 32804257) ^ 16402128 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 32804257) ^ 10934752 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 32804257) ^ 1426272 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 32804257) ^ 395232 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 32804257) ^ 183264 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_34068269 : Nat.Prime 34068269 := by
  apply lucas_primality 34068269 (2 : ZMod 34068269)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (37, 1), (17707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (37, 1), (17707, 1)] : List FactorBlock).map factorBlockValue).prod) = 34068269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_37
      · exact prime_fortyFourAP_17707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34068269) ^ 17034134 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34068269) ^ 2620636 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34068269) ^ 920764 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34068269) ^ 1924 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_34091807 : Nat.Prime 34091807 := by
  apply lucas_primality 34091807 (5 : ZMod 34091807)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (89, 1), (27361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (89, 1), (27361, 1)] : List FactorBlock).map factorBlockValue).prod) = 34091807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_89
      · exact prime_fortyFourAP_27361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 34091807) ^ 17045903 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 34091807) ^ 4870258 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 34091807) ^ 383054 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 34091807) ^ 1246 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_34848677 : Nat.Prime 34848677 := by
  apply lucas_primality 34848677 (2 : ZMod 34848677)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8712169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8712169, 1)] : List FactorBlock).map factorBlockValue).prod) = 34848677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_8712169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 34848677) ^ 17424338 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34848677) ^ 4 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_35140247 : Nat.Prime 35140247 := by
  apply lucas_primality 35140247 (5 : ZMod 35140247)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17570123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17570123, 1)] : List FactorBlock).map factorBlockValue).prod) = 35140247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_17570123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 35140247) ^ 17570123 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 35140247) ^ 2 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_48915121 : Nat.Prime 48915121 := by
  apply lucas_primality 48915121 (14 : ZMod 48915121)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (17, 1), (19, 1), (631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (17, 1), (19, 1), (631, 1)] : List FactorBlock).map factorBlockValue).prod) = 48915121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 48915121) ^ 24457560 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (14 : ZMod 48915121) ^ 16305040 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (14 : ZMod 48915121) ^ 9783024 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (14 : ZMod 48915121) ^ 2877360 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (14 : ZMod 48915121) ^ 2574480 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (14 : ZMod 48915121) ^ 77520 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_51234637 : Nat.Prime 51234637 := by
  apply lucas_primality 51234637 (2 : ZMod 51234637)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (647, 1), (6599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (647, 1), (6599, 1)] : List FactorBlock).map factorBlockValue).prod) = 51234637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_647
      · exact prime_fortyFourAP_6599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51234637) ^ 25617318 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 51234637) ^ 17078212 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 51234637) ^ 79188 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 51234637) ^ 7764 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_53908471 : Nat.Prime 53908471 := by
  apply lucas_primality 53908471 (3 : ZMod 53908471)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (11, 1), (2593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (11, 1), (2593, 1)] : List FactorBlock).map factorBlockValue).prod) = 53908471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_2593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 53908471) ^ 26954235 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 53908471) ^ 17969490 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 53908471) ^ 10781694 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 53908471) ^ 7701210 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 53908471) ^ 4900770 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 53908471) ^ 20790 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_55379759 : Nat.Prime 55379759 := by
  apply lucas_primality 55379759 (7 : ZMod 55379759)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (83, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (83, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod) = 55379759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_83
      · exact prime_fortyFourAP_47659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 55379759) ^ 27689879 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 55379759) ^ 7911394 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 55379759) ^ 667226 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 55379759) ^ 1162 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_60308257 : Nat.Prime 60308257 := by
  apply lucas_primality 60308257 (5 : ZMod 60308257)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (643, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (643, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) = 60308257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_643
      · exact prime_fortyFourAP_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 60308257) ^ 30154128 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 60308257) ^ 20102752 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 60308257) ^ 93792 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 60308257) ^ 61728 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_60338441 : Nat.Prime 60338441 := by
  apply lucas_primality 60338441 (3 : ZMod 60338441)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (17, 1), (89, 1), (997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (17, 1), (89, 1), (997, 1)] : List FactorBlock).map factorBlockValue).prod) = 60338441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_89
      · exact prime_fortyFourAP_997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 60338441) ^ 30169220 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 60338441) ^ 12067688 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 60338441) ^ 3549320 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 60338441) ^ 677960 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 60338441) ^ 60520 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_61359533 : Nat.Prime 61359533 := by
  apply lucas_primality 61359533 (2 : ZMod 61359533)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (1179991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (1179991, 1)] : List FactorBlock).map factorBlockValue).prod) = 61359533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_1179991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 61359533) ^ 30679766 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 61359533) ^ 4719964 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 61359533) ^ 52 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_72158159 : Nat.Prime 72158159 := by
  apply lucas_primality 72158159 (13 : ZMod 72158159)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) = 72158159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_1901
      · exact prime_fortyFourAP_18979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 72158159) ^ 36079079 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 37958 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 3802 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_74144261 : Nat.Prime 74144261 := by
  apply lucas_primality 74144261 (2 : ZMod 74144261)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3707213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3707213, 1)] : List FactorBlock).map factorBlockValue).prod) = 74144261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_3707213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 74144261) ^ 37072130 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 74144261) ^ 14828852 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 74144261) ^ 20 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_75111599 : Nat.Prime 75111599 := by
  apply lucas_primality 75111599 (17 : ZMod 75111599)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (73, 1), (27077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (73, 1), (27077, 1)] : List FactorBlock).map factorBlockValue).prod) = 75111599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_73
      · exact prime_fortyFourAP_27077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 75111599) ^ 37555799 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (17 : ZMod 75111599) ^ 3953242 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (17 : ZMod 75111599) ^ 1028926 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (17 : ZMod 75111599) ^ 2774 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_79077541 : Nat.Prime 79077541 := by
  apply lucas_primality 79077541 (2 : ZMod 79077541)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (77527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (77527, 1)] : List FactorBlock).map factorBlockValue).prod) = 79077541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_77527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79077541) ^ 39538770 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 79077541) ^ 26359180 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 79077541) ^ 15815508 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 79077541) ^ 4651620 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 79077541) ^ 1020 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_80744533 : Nat.Prime 80744533 := by
  apply lucas_primality 80744533 (6 : ZMod 80744533)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (151, 1), (4051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (151, 1), (4051, 1)] : List FactorBlock).map factorBlockValue).prod) = 80744533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_151
      · exact prime_fortyFourAP_4051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 80744533) ^ 40372266 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 80744533) ^ 26914844 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 80744533) ^ 7340412 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 80744533) ^ 534732 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 80744533) ^ 19932 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_82829689 : Nat.Prime 82829689 := by
  apply lucas_primality 82829689 (7 : ZMod 82829689)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (67, 1), (51511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (67, 1), (51511, 1)] : List FactorBlock).map factorBlockValue).prod) = 82829689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_67
      · exact prime_fortyFourAP_51511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 82829689) ^ 41414844 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 82829689) ^ 27609896 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 82829689) ^ 1236264 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 82829689) ^ 1608 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_91432559 : Nat.Prime 91432559 := by
  apply lucas_primality 91432559 (7 : ZMod 91432559)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (599, 1), (10903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (599, 1), (10903, 1)] : List FactorBlock).map factorBlockValue).prod) = 91432559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_599
      · exact prime_fortyFourAP_10903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 91432559) ^ 45716279 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 91432559) ^ 13061794 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 91432559) ^ 152642 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 91432559) ^ 8386 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_98695889 : Nat.Prime 98695889 := by
  apply lucas_primality 98695889 (3 : ZMod 98695889)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (967, 1), (6379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (967, 1), (6379, 1)] : List FactorBlock).map factorBlockValue).prod) = 98695889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_967
      · exact prime_fortyFourAP_6379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 98695889) ^ 49347944 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 98695889) ^ 102064 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 98695889) ^ 15472 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_107890579 : Nat.Prime 107890579 := by
  apply lucas_primality 107890579 (3 : ZMod 107890579)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (61, 1), (97, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (61, 1), (97, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) = 107890579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_61
      · exact prime_fortyFourAP_97
      · exact prime_fortyFourAP_1013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 107890579) ^ 53945289 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 107890579) ^ 35963526 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 107890579) ^ 1768698 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 107890579) ^ 1112274 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 107890579) ^ 106506 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_118826887 : Nat.Prime 118826887 := by
  apply lucas_primality 118826887 (6 : ZMod 118826887)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19804481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19804481, 1)] : List FactorBlock).map factorBlockValue).prod) = 118826887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_19804481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 118826887) ^ 59413443 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 118826887) ^ 39608962 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 118826887) ^ 6 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_119861641 : Nat.Prime 119861641 := by
  apply lucas_primality 119861641 (31 : ZMod 119861641)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (29, 1), (43, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (29, 1), (43, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) = 119861641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_43
      · exact prime_fortyFourAP_89
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 119861641) ^ 59930820 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (31 : ZMod 119861641) ^ 39953880 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (31 : ZMod 119861641) ^ 23972328 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (31 : ZMod 119861641) ^ 4133160 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (31 : ZMod 119861641) ^ 2787480 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (31 : ZMod 119861641) ^ 1346760 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_127435031 : Nat.Prime 127435031 := by
  apply lucas_primality 127435031 (11 : ZMod 127435031)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (163, 1), (2113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (163, 1), (2113, 1)] : List FactorBlock).map factorBlockValue).prod) = 127435031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_37
      · exact prime_fortyFourAP_163
      · exact prime_fortyFourAP_2113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 127435031) ^ 63717515 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 127435031) ^ 25487006 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 127435031) ^ 3444190 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 127435031) ^ 781810 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 127435031) ^ 60310 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_134406001 : Nat.Prime 134406001 := by
  apply lucas_primality 134406001 (17 : ZMod 134406001)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 3), (19, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 3), (19, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) = 134406001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 134406001) ^ 67203000 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (17 : ZMod 134406001) ^ 44802000 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (17 : ZMod 134406001) ^ 26881200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (17 : ZMod 134406001) ^ 7074000 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (17 : ZMod 134406001) ^ 1026000 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_135668537 : Nat.Prime 135668537 := by
  apply lucas_primality 135668537 (3 : ZMod 135668537)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (269, 1), (2741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (269, 1), (2741, 1)] : List FactorBlock).map factorBlockValue).prod) = 135668537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_23
      · exact prime_fortyFourAP_269
      · exact prime_fortyFourAP_2741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 135668537) ^ 67834268 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 135668537) ^ 5898632 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 135668537) ^ 504344 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 135668537) ^ 49496 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_144417341 : Nat.Prime 144417341 := by
  apply lucas_primality 144417341 (2 : ZMod 144417341)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod) = 144417341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7220867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 144417341) ^ 72208670 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 28883468 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 20 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_149316581 : Nat.Prime 149316581 := by
  apply lucas_primality 149316581 (3 : ZMod 149316581)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (139, 1), (7673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (139, 1), (7673, 1)] : List FactorBlock).map factorBlockValue).prod) = 149316581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_139
      · exact prime_fortyFourAP_7673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 149316581) ^ 74658290 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 149316581) ^ 29863316 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 149316581) ^ 21330940 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 149316581) ^ 1074220 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 149316581) ^ 19460 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_157696507 : Nat.Prime 157696507 := by
  apply lucas_primality 157696507 (2 : ZMod 157696507)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (796447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (796447, 1)] : List FactorBlock).map factorBlockValue).prod) = 157696507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_796447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 157696507) ^ 78848253 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 157696507) ^ 52565502 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 157696507) ^ 14336046 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 157696507) ^ 198 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_161379451 : Nat.Prime 161379451 := by
  apply lucas_primality 161379451 (2 : ZMod 161379451)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (71, 1), (5051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (71, 1), (5051, 1)] : List FactorBlock).map factorBlockValue).prod) = 161379451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_71
      · exact prime_fortyFourAP_5051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161379451) ^ 80689725 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161379451) ^ 53793150 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161379451) ^ 32275890 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161379451) ^ 2272950 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161379451) ^ 31950 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_180892039 : Nat.Prime 180892039 := by
  apply lucas_primality 180892039 (3 : ZMod 180892039)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (814829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (814829, 1)] : List FactorBlock).map factorBlockValue).prod) = 180892039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_37
      · exact prime_fortyFourAP_814829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 180892039) ^ 90446019 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 180892039) ^ 60297346 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 180892039) ^ 4888974 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 180892039) ^ 222 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_185725429 : Nat.Prime 185725429 := by
  apply lucas_primality 185725429 (2 : ZMod 185725429)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (43, 1), (51419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (43, 1), (51419, 1)] : List FactorBlock).map factorBlockValue).prod) = 185725429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_43
      · exact prime_fortyFourAP_51419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 185725429) ^ 92862714 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 185725429) ^ 61908476 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 185725429) ^ 26532204 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 185725429) ^ 4319196 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 185725429) ^ 3612 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_188131817 : Nat.Prime 188131817 := by
  apply lucas_primality 188131817 (3 : ZMod 188131817)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (810913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (810913, 1)] : List FactorBlock).map factorBlockValue).prod) = 188131817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_810913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 188131817) ^ 94065908 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 188131817) ^ 6487304 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 188131817) ^ 232 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_190480541 : Nat.Prime 190480541 := by
  apply lucas_primality 190480541 (2 : ZMod 190480541)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (43, 1), (221489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (43, 1), (221489, 1)] : List FactorBlock).map factorBlockValue).prod) = 190480541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_43
      · exact prime_fortyFourAP_221489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 190480541) ^ 95240270 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 190480541) ^ 38096108 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 190480541) ^ 4429780 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 190480541) ^ 860 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_204938549 : Nat.Prime 204938549 := by
  apply lucas_primality 204938549 (2 : ZMod 204938549)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (51234637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (51234637, 1)] : List FactorBlock).map factorBlockValue).prod) = 204938549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_51234637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 204938549) ^ 102469274 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 204938549) ^ 4 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_191
      · exact prime_fortyFourAP_383
      · exact prime_fortyFourAP_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_248990851 : Nat.Prime 248990851 := by
  apply lucas_primality 248990851 (3 : ZMod 248990851)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (89, 1), (6217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (89, 1), (6217, 1)] : List FactorBlock).map factorBlockValue).prod) = 248990851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_89
      · exact prime_fortyFourAP_6217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 248990851) ^ 124495425 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 248990851) ^ 82996950 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 248990851) ^ 49798170 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 248990851) ^ 2797650 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 248990851) ^ 40050 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_251922637 : Nat.Prime 251922637 := by
  apply lucas_primality 251922637 (2 : ZMod 251922637)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (7, 1), (277, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (7, 1), (277, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod) = 251922637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_277
      · exact prime_fortyFourAP_401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 251922637) ^ 125961318 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 251922637) ^ 83974212 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 251922637) ^ 35988948 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 251922637) ^ 909468 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 251922637) ^ 628236 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_277100209 : Nat.Prime 277100209 := by
  apply lucas_primality 277100209 (17 : ZMod 277100209)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) = 277100209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_67
      · exact prime_fortyFourAP_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 277100209) ^ 138550104 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 92366736 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 39585744 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 25190928 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 4135824 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 742896 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_279180007 : Nat.Prime 279180007 := by
  apply lucas_primality 279180007 (3 : ZMod 279180007)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (89, 1), (74687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (89, 1), (74687, 1)] : List FactorBlock).map factorBlockValue).prod) = 279180007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_89
      · exact prime_fortyFourAP_74687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 279180007) ^ 139590003 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 279180007) ^ 93060002 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 279180007) ^ 39882858 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 279180007) ^ 3136854 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 279180007) ^ 3738 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_289278289 : Nat.Prime 289278289 := by
  apply lucas_primality 289278289 (7 : ZMod 289278289)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (13, 1), (41, 1), (3769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (13, 1), (41, 1), (3769, 1)] : List FactorBlock).map factorBlockValue).prod) = 289278289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_41
      · exact prime_fortyFourAP_3769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 289278289) ^ 144639144 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 289278289) ^ 96426096 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 289278289) ^ 22252176 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 289278289) ^ 7055568 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 289278289) ^ 76752 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_313629971 : Nat.Prime 313629971 := by
  apply lucas_primality 313629971 (2 : ZMod 313629971)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (173, 1), (199, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (173, 1), (199, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) = 313629971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_173
      · exact prime_fortyFourAP_199
      · exact prime_fortyFourAP_911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 313629971) ^ 156814985 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 313629971) ^ 62725994 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 313629971) ^ 1812890 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 313629971) ^ 1576030 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 313629971) ^ 344270 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_328801117 : Nat.Prime 328801117 := by
  apply lucas_primality 328801117 (5 : ZMod 328801117)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (109, 1), (35911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (109, 1), (35911, 1)] : List FactorBlock).map factorBlockValue).prod) = 328801117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_109
      · exact prime_fortyFourAP_35911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 328801117) ^ 164400558 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 328801117) ^ 109600372 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 328801117) ^ 46971588 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 328801117) ^ 3016524 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 328801117) ^ 9156 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_343501679 : Nat.Prime 343501679 := by
  apply lucas_primality 343501679 (11 : ZMod 343501679)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (13211603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (13211603, 1)] : List FactorBlock).map factorBlockValue).prod) = 343501679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_13211603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 343501679) ^ 171750839 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 343501679) ^ 26423206 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 343501679) ^ 26 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_369688933 : Nat.Prime 369688933 := by
  apply lucas_primality 369688933 (5 : ZMod 369688933)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (10269137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (10269137, 1)] : List FactorBlock).map factorBlockValue).prod) = 369688933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_10269137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 369688933) ^ 184844466 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 369688933) ^ 123229644 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 369688933) ^ 36 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_380961083 : Nat.Prime 380961083 := by
  apply lucas_primality 380961083 (2 : ZMod 380961083)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (190480541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (190480541, 1)] : List FactorBlock).map factorBlockValue).prod) = 380961083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_190480541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 380961083) ^ 190480541 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 380961083) ^ 2 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_426605947 : Nat.Prime 426605947 := by
  apply lucas_primality 426605947 (2 : ZMod 426605947)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (761, 1), (7187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (761, 1), (7187, 1)] : List FactorBlock).map factorBlockValue).prod) = 426605947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_761
      · exact prime_fortyFourAP_7187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 426605947) ^ 213302973 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 426605947) ^ 142201982 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 426605947) ^ 32815842 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 426605947) ^ 560586 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 426605947) ^ 59358 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_451071857 : Nat.Prime 451071857 := by
  apply lucas_primality 451071857 (3 : ZMod 451071857)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (163, 1), (9103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (163, 1), (9103, 1)] : List FactorBlock).map factorBlockValue).prod) = 451071857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_163
      · exact prime_fortyFourAP_9103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 451071857) ^ 225535928 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 451071857) ^ 23740624 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 451071857) ^ 2767312 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 451071857) ^ 49552 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_466873793 : Nat.Prime 466873793 := by
  apply lucas_primality 466873793 (3 : ZMod 466873793)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (11, 1), (211, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (11, 1), (211, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) = 466873793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_211
      · exact prime_fortyFourAP_449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 466873793) ^ 233436896 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 466873793) ^ 66696256 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 466873793) ^ 42443072 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 466873793) ^ 2212672 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 466873793) ^ 1039808 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_533624659 : Nat.Prime 533624659 := by
  apply lucas_primality 533624659 (7 : ZMod 533624659)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (12705349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (12705349, 1)] : List FactorBlock).map factorBlockValue).prod) = 533624659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_12705349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 533624659) ^ 266812329 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 533624659) ^ 177874886 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 533624659) ^ 76232094 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 533624659) ^ 42 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_566707819 : Nat.Prime 566707819 := by
  apply lucas_primality 566707819 (3 : ZMod 566707819)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (1709, 1), (3251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (1709, 1), (3251, 1)] : List FactorBlock).map factorBlockValue).prod) = 566707819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_1709
      · exact prime_fortyFourAP_3251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 566707819) ^ 283353909 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 566707819) ^ 188902606 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 566707819) ^ 33335754 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 566707819) ^ 331602 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 566707819) ^ 174318 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_651175513 : Nat.Prime 651175513 := by
  apply lucas_primality 651175513 (11 : ZMod 651175513)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (29, 1), (79, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (29, 1), (79, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) = 651175513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_79
      · exact prime_fortyFourAP_911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 651175513) ^ 325587756 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 651175513) ^ 217058504 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 651175513) ^ 50090424 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 651175513) ^ 22454328 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 651175513) ^ 8242728 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 651175513) ^ 714792 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_673639457 : Nat.Prime 673639457 := by
  apply lucas_primality 673639457 (6 : ZMod 673639457)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 2), (23, 1), (18679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 2), (23, 1), (18679, 1)] : List FactorBlock).map factorBlockValue).prod) = 673639457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_23
      · exact prime_fortyFourAP_18679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 673639457) ^ 336819728 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 673639457) ^ 96234208 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 673639457) ^ 29288672 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 673639457) ^ 36064 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_738639761 : Nat.Prime 738639761 := by
  apply lucas_primality 738639761 (3 : ZMod 738639761)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (499, 1), (18503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (499, 1), (18503, 1)] : List FactorBlock).map factorBlockValue).prod) = 738639761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_499
      · exact prime_fortyFourAP_18503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 738639761) ^ 369319880 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 738639761) ^ 147727952 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 738639761) ^ 1480240 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 738639761) ^ 39920 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_840785173 : Nat.Prime 840785173 := by
  apply lucas_primality 840785173 (2 : ZMod 840785173)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2969, 1), (23599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2969, 1), (23599, 1)] : List FactorBlock).map factorBlockValue).prod) = 840785173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_2969
      · exact prime_fortyFourAP_23599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 840785173) ^ 420392586 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 840785173) ^ 280261724 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 840785173) ^ 283188 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 840785173) ^ 35628 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_889731133 : Nat.Prime 889731133 := by
  apply lucas_primality 889731133 (2 : ZMod 889731133)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (74144261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (74144261, 1)] : List FactorBlock).map factorBlockValue).prod) = 889731133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_74144261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 889731133) ^ 444865566 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 889731133) ^ 296577044 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 889731133) ^ 12 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_938917687 : Nat.Prime 938917687 := by
  apply lucas_primality 938917687 (3 : ZMod 938917687)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (79, 1), (282977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (79, 1), (282977, 1)] : List FactorBlock).map factorBlockValue).prod) = 938917687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_79
      · exact prime_fortyFourAP_282977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 938917687) ^ 469458843 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 938917687) ^ 312972562 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 938917687) ^ 134131098 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 938917687) ^ 11885034 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 938917687) ^ 3318 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_963143029 : Nat.Prime 963143029 := by
  apply lucas_primality 963143029 (2 : ZMod 963143029)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (8917991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (8917991, 1)] : List FactorBlock).map factorBlockValue).prod) = 963143029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_8917991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 963143029) ^ 481571514 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 963143029) ^ 321047676 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 963143029) ^ 108 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_964340411 : Nat.Prime 964340411 := by
  apply lucas_primality 964340411 (6 : ZMod 964340411)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (1249, 1), (7019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (1249, 1), (7019, 1)] : List FactorBlock).map factorBlockValue).prod) = 964340411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_1249
      · exact prime_fortyFourAP_7019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 964340411) ^ 482170205 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 964340411) ^ 192868082 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 964340411) ^ 87667310 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 964340411) ^ 772090 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 964340411) ^ 137390 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_982266581 : Nat.Prime 982266581 := by
  apply lucas_primality 982266581 (2 : ZMod 982266581)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (109, 1), (450581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (109, 1), (450581, 1)] : List FactorBlock).map factorBlockValue).prod) = 982266581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_109
      · exact prime_fortyFourAP_450581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 982266581) ^ 491133290 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 982266581) ^ 196453316 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 982266581) ^ 9011620 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 982266581) ^ 2180 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1138844891 : Nat.Prime 1138844891 := by
  apply lucas_primality 1138844891 (2 : ZMod 1138844891)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (89, 1), (1279601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (89, 1), (1279601, 1)] : List FactorBlock).map factorBlockValue).prod) = 1138844891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_89
      · exact prime_fortyFourAP_1279601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1138844891) ^ 569422445 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1138844891) ^ 227768978 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1138844891) ^ 12796010 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1138844891) ^ 890 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_113
      · exact prime_fortyFourAP_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1244799989 : Nat.Prime 1244799989 := by
  apply lucas_primality 1244799989 (2 : ZMod 1244799989)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (181, 1), (1719337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (181, 1), (1719337, 1)] : List FactorBlock).map factorBlockValue).prod) = 1244799989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_181
      · exact prime_fortyFourAP_1719337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1244799989) ^ 622399994 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1244799989) ^ 6877348 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1244799989) ^ 724 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1256579221 : Nat.Prime 1256579221 := by
  apply lucas_primality 1256579221 (6 : ZMod 1256579221)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 2), (123923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 2), (123923, 1)] : List FactorBlock).map factorBlockValue).prod) = 1256579221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_123923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1256579221) ^ 628289610 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1256579221) ^ 418859740 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1256579221) ^ 251315844 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1256579221) ^ 96659940 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1256579221) ^ 10140 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1440461809 : Nat.Prime 1440461809 := by
  apply lucas_primality 1440461809 (7 : ZMod 1440461809)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1440461809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_61
      · exact prime_fortyFourAP_163987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1440461809) ^ 720230904 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 480153936 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 23614128 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 8784 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1596258817 : Nat.Prime 1596258817 := by
  apply lucas_primality 1596258817 (5 : ZMod 1596258817)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (191, 1), (5441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (191, 1), (5441, 1)] : List FactorBlock).map factorBlockValue).prod) = 1596258817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_191
      · exact prime_fortyFourAP_5441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1596258817) ^ 798129408 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1596258817) ^ 532086272 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1596258817) ^ 8357376 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1596258817) ^ 293376 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1904284259 : Nat.Prime 1904284259 := by
  apply lucas_primality 1904284259 (2 : ZMod 1904284259)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29873, 1), (31873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29873, 1), (31873, 1)] : List FactorBlock).map factorBlockValue).prod) = 1904284259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_29873
      · exact prime_fortyFourAP_31873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1904284259) ^ 952142129 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1904284259) ^ 63746 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1904284259) ^ 59746 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2062421371 : Nat.Prime 2062421371 := by
  apply lucas_primality 2062421371 (2 : ZMod 2062421371)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (22915793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (22915793, 1)] : List FactorBlock).map factorBlockValue).prod) = 2062421371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_22915793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2062421371) ^ 1031210685 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2062421371) ^ 687473790 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2062421371) ^ 412484274 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2062421371) ^ 90 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2064319931 : Nat.Prime 2064319931 := by
  apply lucas_primality 2064319931 (2 : ZMod 2064319931)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (401, 1), (514793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (401, 1), (514793, 1)] : List FactorBlock).map factorBlockValue).prod) = 2064319931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_401
      · exact prime_fortyFourAP_514793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2064319931) ^ 1032159965 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2064319931) ^ 412863986 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2064319931) ^ 5147930 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2064319931) ^ 4010 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2170704469 : Nat.Prime 2170704469 := by
  apply lucas_primality 2170704469 (6 : ZMod 2170704469)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (180892039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (180892039, 1)] : List FactorBlock).map factorBlockValue).prod) = 2170704469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_180892039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 2170704469) ^ 1085352234 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2170704469) ^ 723568156 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2170704469) ^ 12 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2278167139 : Nat.Prime 2278167139 := by
  apply lucas_primality 2278167139 (2 : ZMod 2278167139)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (1553, 1), (6269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (1553, 1), (6269, 1)] : List FactorBlock).map factorBlockValue).prod) = 2278167139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_1553
      · exact prime_fortyFourAP_6269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2278167139) ^ 1139083569 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2278167139) ^ 759389046 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2278167139) ^ 175243626 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2278167139) ^ 1466946 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2278167139) ^ 363402 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2285686021 : Nat.Prime 2285686021 := by
  apply lucas_primality 2285686021 (6 : ZMod 2285686021)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (3221, 1), (11827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (3221, 1), (11827, 1)] : List FactorBlock).map factorBlockValue).prod) = 2285686021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_3221
      · exact prime_fortyFourAP_11827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2285686021) ^ 1142843010 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2285686021) ^ 761895340 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2285686021) ^ 457137204 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2285686021) ^ 709620 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2285686021) ^ 193260 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2418018503 : Nat.Prime 2418018503 := by
  apply lucas_primality 2418018503 (5 : ZMod 2418018503)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (631, 1), (1916021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (631, 1), (1916021, 1)] : List FactorBlock).map factorBlockValue).prod) = 2418018503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_631
      · exact prime_fortyFourAP_1916021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2418018503) ^ 1209009251 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2418018503) ^ 3832042 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2418018503) ^ 1262 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2586028147 : Nat.Prime 2586028147 := by
  apply lucas_primality 2586028147 (3 : ZMod 2586028147)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (4273, 1), (7759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (4273, 1), (7759, 1)] : List FactorBlock).map factorBlockValue).prod) = 2586028147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_4273
      · exact prime_fortyFourAP_7759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2586028147) ^ 1293014073 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2586028147) ^ 862009382 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2586028147) ^ 198925242 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2586028147) ^ 605202 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2586028147) ^ 333294 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2681741641 : Nat.Prime 2681741641 := by
  apply lucas_primality 2681741641 (13 : ZMod 2681741641)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (883, 1), (25309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (883, 1), (25309, 1)] : List FactorBlock).map factorBlockValue).prod) = 2681741641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_883
      · exact prime_fortyFourAP_25309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2681741641) ^ 1340870820 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 2681741641) ^ 893913880 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 2681741641) ^ 536348328 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 2681741641) ^ 3037080 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 2681741641) ^ 105960 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2838522053 : Nat.Prime 2838522053 := by
  apply lucas_primality 2838522053 (2 : ZMod 2838522053)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (3715343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (3715343, 1)] : List FactorBlock).map factorBlockValue).prod) = 2838522053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_191
      · exact prime_fortyFourAP_3715343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2838522053) ^ 1419261026 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2838522053) ^ 14861372 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2838522053) ^ 764 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2848589311 : Nat.Prime 2848589311 := by
  apply lucas_primality 2848589311 (6 : ZMod 2848589311)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (107, 1), (331, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (107, 1), (331, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) = 2848589311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_107
      · exact prime_fortyFourAP_331
      · exact prime_fortyFourAP_383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2848589311) ^ 1424294655 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 949529770 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 569717862 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 406941330 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 26622330 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 8606010 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 7437570 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2871090773 : Nat.Prime 2871090773 := by
  apply lucas_primality 2871090773 (2 : ZMod 2871090773)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (53, 1), (1231171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (53, 1), (1231171, 1)] : List FactorBlock).map factorBlockValue).prod) = 2871090773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_53
      · exact prime_fortyFourAP_1231171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2871090773) ^ 1435545386 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871090773) ^ 261008252 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871090773) ^ 54171524 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871090773) ^ 2332 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2976375529 : Nat.Prime 2976375529 := by
  apply lucas_primality 2976375529 (19 : ZMod 2976375529)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (5905507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (5905507, 1)] : List FactorBlock).map factorBlockValue).prod) = 2976375529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_5905507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 2976375529) ^ 1488187764 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2976375529) ^ 992125176 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2976375529) ^ 425196504 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2976375529) ^ 504 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_3409382089 : Nat.Prime 3409382089 := by
  apply lucas_primality 3409382089 (29 : ZMod 3409382089)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (107, 1), (191, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (107, 1), (191, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) = 3409382089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_107
      · exact prime_fortyFourAP_191
      · exact prime_fortyFourAP_331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 3409382089) ^ 1704691044 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (29 : ZMod 3409382089) ^ 1136460696 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (29 : ZMod 3409382089) ^ 487054584 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (29 : ZMod 3409382089) ^ 31863384 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (29 : ZMod 3409382089) ^ 17850168 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (29 : ZMod 3409382089) ^ 10300248 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_3866391601 : Nat.Prime 3866391601 := by
  apply lucas_primality 3866391601 (13 : ZMod 3866391601)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (17, 1), (189529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (17, 1), (189529, 1)] : List FactorBlock).map factorBlockValue).prod) = 3866391601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_189529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3866391601) ^ 1933195800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 3866391601) ^ 1288797200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 3866391601) ^ 773278320 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 3866391601) ^ 227434800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 3866391601) ^ 20400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_3873642503 : Nat.Prime 3873642503 := by
  apply lucas_primality 3873642503 (5 : ZMod 3873642503)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (269, 1), (443, 1), (16253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (269, 1), (443, 1), (16253, 1)] : List FactorBlock).map factorBlockValue).prod) = 3873642503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_269
      · exact prime_fortyFourAP_443
      · exact prime_fortyFourAP_16253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3873642503) ^ 1936821251 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3873642503) ^ 14400158 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3873642503) ^ 8744114 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3873642503) ^ 238334 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_4988251591 : Nat.Prime 4988251591 := by
  apply lucas_primality 4988251591 (11 : ZMod 4988251591)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (167, 1), (142237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (167, 1), (142237, 1)] : List FactorBlock).map factorBlockValue).prod) = 4988251591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_167
      · exact prime_fortyFourAP_142237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4988251591) ^ 2494125795 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 4988251591) ^ 1662750530 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 4988251591) ^ 997650318 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 4988251591) ^ 712607370 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 4988251591) ^ 29869770 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 4988251591) ^ 35070 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_5118840821 : Nat.Prime 5118840821 := by
  apply lucas_primality 5118840821 (2 : ZMod 5118840821)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1291, 1), (198251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1291, 1), (198251, 1)] : List FactorBlock).map factorBlockValue).prod) = 5118840821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_1291
      · exact prime_fortyFourAP_198251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5118840821) ^ 2559420410 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5118840821) ^ 1023768164 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5118840821) ^ 3965020 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5118840821) ^ 25820 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_5789592673 : Nat.Prime 5789592673 := by
  apply lucas_primality 5789592673 (10 : ZMod 5789592673)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (60308257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (60308257, 1)] : List FactorBlock).map factorBlockValue).prod) = 5789592673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_60308257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 5789592673) ^ 2894796336 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 5789592673) ^ 1929864224 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 5789592673) ^ 96 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_5839099949 : Nat.Prime 5839099949 := by
  apply lucas_primality 5839099949 (2 : ZMod 5839099949)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (647, 1), (205111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (647, 1), (205111, 1)] : List FactorBlock).map factorBlockValue).prod) = 5839099949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_647
      · exact prime_fortyFourAP_205111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5839099949) ^ 2919549974 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5839099949) ^ 530827268 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5839099949) ^ 9024884 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5839099949) ^ 28468 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_6076909123 : Nat.Prime 6076909123 := by
  apply lucas_primality 6076909123 (5 : ZMod 6076909123)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (239, 1), (4237733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (239, 1), (4237733, 1)] : List FactorBlock).map factorBlockValue).prod) = 6076909123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_239
      · exact prime_fortyFourAP_4237733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6076909123) ^ 3038454561 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 6076909123) ^ 2025636374 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 6076909123) ^ 25426398 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 6076909123) ^ 1434 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_6385035269 : Nat.Prime 6385035269 := by
  apply lucas_primality 6385035269 (2 : ZMod 6385035269)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1596258817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1596258817, 1)] : List FactorBlock).map factorBlockValue).prod) = 6385035269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_1596258817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 6385035269) ^ 3192517634 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6385035269) ^ 4 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_7088013991 : Nat.Prime 7088013991 := by
  apply lucas_primality 7088013991 (11 : ZMod 7088013991)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (41, 1), (151, 1), (12721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (41, 1), (151, 1), (12721, 1)] : List FactorBlock).map factorBlockValue).prod) = 7088013991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_41
      · exact prime_fortyFourAP_151
      · exact prime_fortyFourAP_12721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 7088013991) ^ 3544006995 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 2362671330 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 1417602798 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 172878390 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 46940490 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 557190 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_8775342271 : Nat.Prime 8775342271 := by
  apply lucas_primality 8775342271 (3 : ZMod 8775342271)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (47, 1), (61, 1), (71, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (47, 1), (61, 1), (71, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) = 8775342271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_61
      · exact prime_fortyFourAP_71
      · exact prime_fortyFourAP_479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8775342271) ^ 4387671135 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8775342271) ^ 2925114090 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8775342271) ^ 1755068454 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8775342271) ^ 186709410 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8775342271) ^ 143858070 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8775342271) ^ 123596370 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8775342271) ^ 18320130 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_10438235413 : Nat.Prime 10438235413 := by
  apply lucas_primality 10438235413 (2 : ZMod 10438235413)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (79077541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (79077541, 1)] : List FactorBlock).map factorBlockValue).prod) = 10438235413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_79077541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10438235413) ^ 5219117706 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10438235413) ^ 3479411804 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10438235413) ^ 948930492 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10438235413) ^ 132 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_10697436467 : Nat.Prime 10697436467 := by
  apply lucas_primality 10697436467 (2 : ZMod 10697436467)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (157, 1), (34068269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (157, 1), (34068269, 1)] : List FactorBlock).map factorBlockValue).prod) = 10697436467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_157
      · exact prime_fortyFourAP_34068269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10697436467) ^ 5348718233 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10697436467) ^ 68136538 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10697436467) ^ 314 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_11339536811 : Nat.Prime 11339536811 := by
  apply lucas_primality 11339536811 (6 : ZMod 11339536811)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (5225593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (5225593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11339536811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_31
      · exact prime_fortyFourAP_5225593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 11339536811) ^ 5669768405 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 11339536811) ^ 2267907362 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 11339536811) ^ 1619933830 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 11339536811) ^ 365791510 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 11339536811) ^ 2170 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_14325861287 : Nat.Prime 14325861287 := by
  apply lucas_primality 14325861287 (5 : ZMod 14325861287)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (651175513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (651175513, 1)] : List FactorBlock).map factorBlockValue).prod) = 14325861287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_651175513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 14325861287) ^ 7162930643 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 14325861287) ^ 1302351026 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 14325861287) ^ 22 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_15837208853 : Nat.Prime 15837208853 := by
  apply lucas_primality 15837208853 (2 : ZMod 15837208853)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (9257, 1), (22511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (9257, 1), (22511, 1)] : List FactorBlock).map factorBlockValue).prod) = 15837208853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_9257
      · exact prime_fortyFourAP_22511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15837208853) ^ 7918604426 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 15837208853) ^ 833537308 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 15837208853) ^ 1710836 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 15837208853) ^ 703532 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_18047904481 : Nat.Prime 18047904481 := by
  apply lucas_primality 18047904481 (11 : ZMod 18047904481)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (17, 1), (737251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (17, 1), (737251, 1)] : List FactorBlock).map factorBlockValue).prod) = 18047904481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_737251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 18047904481) ^ 9023952240 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 18047904481) ^ 6015968160 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 18047904481) ^ 3609580896 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 18047904481) ^ 1061641440 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 18047904481) ^ 24480 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_18299340599 : Nat.Prime 18299340599 := by
  apply lucas_primality 18299340599 (7 : ZMod 18299340599)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (118826887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (118826887, 1)] : List FactorBlock).map factorBlockValue).prod) = 18299340599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_118826887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 18299340599) ^ 9149670299 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 18299340599) ^ 2614191514 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 18299340599) ^ 1663576418 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 18299340599) ^ 154 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_19286808221 : Nat.Prime 19286808221 := by
  apply lucas_primality 19286808221 (3 : ZMod 19286808221)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (964340411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (964340411, 1)] : List FactorBlock).map factorBlockValue).prod) = 19286808221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_964340411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 19286808221) ^ 9643404110 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 19286808221) ^ 3857361644 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 19286808221) ^ 20 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_19748623057 : Nat.Prime 19748623057 := by
  apply lucas_primality 19748623057 (10 : ZMod 19748623057)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (67, 1), (157, 1), (39113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (67, 1), (157, 1), (39113, 1)] : List FactorBlock).map factorBlockValue).prod) = 19748623057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_67
      · exact prime_fortyFourAP_157
      · exact prime_fortyFourAP_39113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 19748623057) ^ 9874311528 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 19748623057) ^ 6582874352 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 19748623057) ^ 294755568 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 19748623057) ^ 125787408 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 19748623057) ^ 504912 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_21846394897 : Nat.Prime 21846394897 := by
  apply lucas_primality 21846394897 (5 : ZMod 21846394897)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (31, 1), (14681717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (31, 1), (14681717, 1)] : List FactorBlock).map factorBlockValue).prod) = 21846394897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_31
      · exact prime_fortyFourAP_14681717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 21846394897) ^ 10923197448 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 21846394897) ^ 7282131632 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 21846394897) ^ 704722416 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 21846394897) ^ 1488 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_23241855019 : Nat.Prime 23241855019 := by
  apply lucas_primality 23241855019 (10 : ZMod 23241855019)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3873642503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3873642503, 1)] : List FactorBlock).map factorBlockValue).prod) = 23241855019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_3873642503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 23241855019) ^ 11620927509 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 23241855019) ^ 7747285006 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 23241855019) ^ 6 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_24212266553 : Nat.Prime 24212266553 := by
  apply lucas_primality 24212266553 (3 : ZMod 24212266553)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (139, 1), (21773621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (139, 1), (21773621, 1)] : List FactorBlock).map factorBlockValue).prod) = 24212266553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_139
      · exact prime_fortyFourAP_21773621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 24212266553) ^ 12106133276 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 24212266553) ^ 174188968 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 24212266553) ^ 1112 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_24650302561 : Nat.Prime 24650302561 := by
  apply lucas_primality 24650302561 (7 : ZMod 24650302561)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (13, 1), (71, 1), (55639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (13, 1), (71, 1), (55639, 1)] : List FactorBlock).map factorBlockValue).prod) = 24650302561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_71
      · exact prime_fortyFourAP_55639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 24650302561) ^ 12325151280 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 24650302561) ^ 8216767520 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 24650302561) ^ 4930060512 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 24650302561) ^ 1896177120 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 24650302561) ^ 347187360 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 24650302561) ^ 443040 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_26509117937 : Nat.Prime 26509117937 := by
  apply lucas_primality 26509117937 (3 : ZMod 26509117937)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (821, 1), (288293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (821, 1), (288293, 1)] : List FactorBlock).map factorBlockValue).prod) = 26509117937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_821
      · exact prime_fortyFourAP_288293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26509117937) ^ 13254558968 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 26509117937) ^ 3787016848 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 26509117937) ^ 32288816 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 26509117937) ^ 91952 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_29304298123 : Nat.Prime 29304298123 := by
  apply lucas_primality 29304298123 (2 : ZMod 29304298123)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (1229, 1), (32843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (1229, 1), (32843, 1)] : List FactorBlock).map factorBlockValue).prod) = 29304298123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_1229
      · exact prime_fortyFourAP_32843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29304298123) ^ 14652149061 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 29304298123) ^ 9768099374 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 29304298123) ^ 2664027102 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 29304298123) ^ 23844018 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 29304298123) ^ 892254 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_31945928813 : Nat.Prime 31945928813 := by
  apply lucas_primality 31945928813 (3 : ZMod 31945928813)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (131, 1), (1487, 1), (5857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (131, 1), (1487, 1), (5857, 1)] : List FactorBlock).map factorBlockValue).prod) = 31945928813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_131
      · exact prime_fortyFourAP_1487
      · exact prime_fortyFourAP_5857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 31945928813) ^ 15972964406 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 31945928813) ^ 4563704116 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 31945928813) ^ 243862052 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 31945928813) ^ 21483476 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 31945928813) ^ 5454316 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_32446695341 : Nat.Prime 32446695341 := by
  apply lucas_primality 32446695341 (3 : ZMod 32446695341)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (47, 1), (659, 1), (52379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (47, 1), (659, 1), (52379, 1)] : List FactorBlock).map factorBlockValue).prod) = 32446695341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_659
      · exact prime_fortyFourAP_52379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32446695341) ^ 16223347670 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 32446695341) ^ 6489339068 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 32446695341) ^ 690355220 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 32446695341) ^ 49236260 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 32446695341) ^ 619460 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_36598681199 : Nat.Prime 36598681199 := by
  apply lucas_primality 36598681199 (11 : ZMod 36598681199)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18299340599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18299340599, 1)] : List FactorBlock).map factorBlockValue).prod) = 36598681199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_18299340599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 36598681199) ^ 18299340599 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 36598681199) ^ 2 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_36774401311 : Nat.Prime 36774401311 := by
  apply lucas_primality 36774401311 (7 : ZMod 36774401311)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (31, 1), (13180789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (31, 1), (13180789, 1)] : List FactorBlock).map factorBlockValue).prod) = 36774401311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_31
      · exact prime_fortyFourAP_13180789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 36774401311) ^ 18387200655 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 36774401311) ^ 12258133770 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 36774401311) ^ 7354880262 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 36774401311) ^ 1186271010 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 36774401311) ^ 2790 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_151
      · exact prime_fortyFourAP_479
      · exact prime_fortyFourAP_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_49882515911 : Nat.Prime 49882515911 := by
  apply lucas_primality 49882515911 (7 : ZMod 49882515911)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4988251591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4988251591, 1)] : List FactorBlock).map factorBlockValue).prod) = 49882515911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_4988251591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 49882515911) ^ 24941257955 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 49882515911) ^ 9976503182 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 49882515911) ^ 10 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_53839808623 : Nat.Prime 53839808623 := by
  apply lucas_primality 53839808623 (3 : ZMod 53839808623)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (19, 1), (3086791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (19, 1), (3086791, 1)] : List FactorBlock).map factorBlockValue).prod) = 53839808623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_3086791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 53839808623) ^ 26919904311 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 53839808623) ^ 17946602874 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 53839808623) ^ 3167047566 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 53839808623) ^ 2833674138 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 53839808623) ^ 17442 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_54619219163 : Nat.Prime 54619219163 := by
  apply lucas_primality 54619219163 (2 : ZMod 54619219163)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (199, 1), (307, 1), (9511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (199, 1), (307, 1), (9511, 1)] : List FactorBlock).map factorBlockValue).prod) = 54619219163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_199
      · exact prime_fortyFourAP_307
      · exact prime_fortyFourAP_9511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 54619219163) ^ 27309609581 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 54619219163) ^ 1162111046 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 54619219163) ^ 274468438 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 54619219163) ^ 177912766 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 54619219163) ^ 5742742 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_54819625657 : Nat.Prime 54819625657 := by
  apply lucas_primality 54819625657 (7 : ZMod 54819625657)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (67, 1), (34091807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (67, 1), (34091807, 1)] : List FactorBlock).map factorBlockValue).prod) = 54819625657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_67
      · exact prime_fortyFourAP_34091807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 54819625657) ^ 27409812828 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 54819625657) ^ 18273208552 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 54819625657) ^ 818203368 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 54819625657) ^ 1608 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_59254815407 : Nat.Prime 59254815407 := by
  apply lucas_primality 59254815407 (5 : ZMod 59254815407)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (3343, 1), (385327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (3343, 1), (385327, 1)] : List FactorBlock).map factorBlockValue).prod) = 59254815407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_23
      · exact prime_fortyFourAP_3343
      · exact prime_fortyFourAP_385327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 59254815407) ^ 29627407703 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 59254815407) ^ 2576296322 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 59254815407) ^ 17725042 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 59254815407) ^ 153778 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_67971064771 : Nat.Prime 67971064771 := by
  apply lucas_primality 67971064771 (2 : ZMod 67971064771)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (107890579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (107890579, 1)] : List FactorBlock).map factorBlockValue).prod) = 67971064771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_107890579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 67971064771) ^ 33985532385 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 67971064771) ^ 22657021590 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 67971064771) ^ 13594212954 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 67971064771) ^ 9710152110 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 67971064771) ^ 630 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_84756586553 : Nat.Prime 84756586553 := by
  apply lucas_primality 84756586553 (3 : ZMod 84756586553)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (963143029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (963143029, 1)] : List FactorBlock).map factorBlockValue).prod) = 84756586553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_963143029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 84756586553) ^ 42378293276 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 84756586553) ^ 7705144232 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 84756586553) ^ 88 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_103039496123 : Nat.Prime 103039496123 := by
  apply lucas_primality 103039496123 (2 : ZMod 103039496123)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (1256579221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (1256579221, 1)] : List FactorBlock).map factorBlockValue).prod) = 103039496123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_41
      · exact prime_fortyFourAP_1256579221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 103039496123) ^ 51519748061 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 103039496123) ^ 2513158442 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 103039496123) ^ 82 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_141929920049 : Nat.Prime 141929920049 := by
  apply lucas_primality 141929920049 (3 : ZMod 141929920049)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (19, 1), (1753, 1), (38047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (19, 1), (1753, 1), (38047, 1)] : List FactorBlock).map factorBlockValue).prod) = 141929920049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_1753
      · exact prime_fortyFourAP_38047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 141929920049) ^ 70964960024 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 141929920049) ^ 20275702864 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 141929920049) ^ 7469995792 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 141929920049) ^ 80964016 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 141929920049) ^ 3730384 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_147601178531 : Nat.Prime 147601178531 := by
  apply lucas_primality 147601178531 (6 : ZMod 147601178531)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (1787, 1), (635363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (1787, 1), (635363, 1)] : List FactorBlock).map factorBlockValue).prod) = 147601178531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_1787
      · exact prime_fortyFourAP_635363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 147601178531) ^ 73800589265 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 147601178531) ^ 29520235706 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 147601178531) ^ 11353936810 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 147601178531) ^ 82597190 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 147601178531) ^ 232310 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_151858876903 : Nat.Prime 151858876903 := by
  apply lucas_primality 151858876903 (3 : ZMod 151858876903)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3793, 1), (6672769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3793, 1), (6672769, 1)] : List FactorBlock).map factorBlockValue).prod) = 151858876903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_3793
      · exact prime_fortyFourAP_6672769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 151858876903) ^ 75929438451 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 151858876903) ^ 50619625634 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 151858876903) ^ 40036614 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 151858876903) ^ 22758 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_151865598659 : Nat.Prime 151865598659 := by
  apply lucas_primality 151865598659 (2 : ZMod 151865598659)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (1244799989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (1244799989, 1)] : List FactorBlock).map factorBlockValue).prod) = 151865598659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_61
      · exact prime_fortyFourAP_1244799989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 151865598659) ^ 75932799329 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 151865598659) ^ 2489599978 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 151865598659) ^ 122 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_172105589911 : Nat.Prime 172105589911 := by
  apply lucas_primality 172105589911 (3 : ZMod 172105589911)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (37, 1), (1021, 1), (8933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (37, 1), (1021, 1), (8933, 1)] : List FactorBlock).map factorBlockValue).prod) = 172105589911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_37
      · exact prime_fortyFourAP_1021
      · exact prime_fortyFourAP_8933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 172105589911) ^ 86052794955 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 172105589911) ^ 57368529970 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 172105589911) ^ 34421117982 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 172105589911) ^ 10123858230 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 172105589911) ^ 4651502430 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 172105589911) ^ 168565710 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 172105589911) ^ 19266270 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_186855762221 : Nat.Prime 186855762221 := by
  apply lucas_primality 186855762221 (3 : ZMod 186855762221)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (191, 1), (48915121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (191, 1), (48915121, 1)] : List FactorBlock).map factorBlockValue).prod) = 186855762221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_191
      · exact prime_fortyFourAP_48915121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 186855762221) ^ 93427881110 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 186855762221) ^ 37371152444 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 186855762221) ^ 978302420 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 186855762221) ^ 3820 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_190507613573 : Nat.Prime 190507613573 := by
  apply lucas_primality 190507613573 (2 : ZMod 190507613573)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (727, 1), (3691, 1), (17749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (727, 1), (3691, 1), (17749, 1)] : List FactorBlock).map factorBlockValue).prod) = 190507613573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_727
      · exact prime_fortyFourAP_3691
      · exact prime_fortyFourAP_17749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 190507613573) ^ 95253806786 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 190507613573) ^ 262046236 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 190507613573) ^ 51614092 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 190507613573) ^ 10733428 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_224916175177 : Nat.Prime 224916175177 := by
  apply lucas_primality 224916175177 (15 : ZMod 224916175177)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (11, 1), (337, 1), (51593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (11, 1), (337, 1), (51593, 1)] : List FactorBlock).map factorBlockValue).prod) = 224916175177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_337
      · exact prime_fortyFourAP_51593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 224916175177) ^ 112458087588 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (15 : ZMod 224916175177) ^ 74972058392 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (15 : ZMod 224916175177) ^ 32130882168 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (15 : ZMod 224916175177) ^ 20446925016 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (15 : ZMod 224916175177) ^ 667407048 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (15 : ZMod 224916175177) ^ 4359432 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_252321361381 : Nat.Prime 252321361381 := by
  apply lucas_primality 252321361381 (2 : ZMod 252321361381)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (11, 1), (127435031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (11, 1), (127435031, 1)] : List FactorBlock).map factorBlockValue).prod) = 252321361381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_127435031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 252321361381) ^ 126160680690 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 252321361381) ^ 84107120460 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 252321361381) ^ 50464272276 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 252321361381) ^ 22938305580 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 252321361381) ^ 1980 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_260519272661 : Nat.Prime 260519272661 := by
  apply lucas_primality 260519272661 (3 : ZMod 260519272661)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (25439, 1), (512047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (25439, 1), (512047, 1)] : List FactorBlock).map factorBlockValue).prod) = 260519272661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_25439
      · exact prime_fortyFourAP_512047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 260519272661) ^ 130259636330 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 260519272661) ^ 52103854532 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 260519272661) ^ 10240940 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 260519272661) ^ 508780 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_331660790141 : Nat.Prime 331660790141 := by
  apply lucas_primality 331660790141 (2 : ZMod 331660790141)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (11933, 1), (73141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (11933, 1), (73141, 1)] : List FactorBlock).map factorBlockValue).prod) = 331660790141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_11933
      · exact prime_fortyFourAP_73141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 331660790141) ^ 165830395070 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 331660790141) ^ 66332158028 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 331660790141) ^ 17455831060 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 331660790141) ^ 27793580 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 331660790141) ^ 4534540 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_362865177953 : Nat.Prime 362865177953 := by
  apply lucas_primality 362865177953 (3 : ZMod 362865177953)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11339536811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11339536811, 1)] : List FactorBlock).map factorBlockValue).prod) = 362865177953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_11339536811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 362865177953) ^ 181432588976 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 362865177953) ^ 32 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_373711524443 : Nat.Prime 373711524443 := by
  apply lucas_primality 373711524443 (2 : ZMod 373711524443)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (186855762221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (186855762221, 1)] : List FactorBlock).map factorBlockValue).prod) = 373711524443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_186855762221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 373711524443) ^ 186855762221 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 373711524443) ^ 2 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_388408415123 : Nat.Prime 388408415123 := by
  apply lucas_primality 388408415123 (2 : ZMod 388408415123)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (479, 1), (1213, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (479, 1), (1213, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) = 388408415123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_479
      · exact prime_fortyFourAP_1213
      · exact prime_fortyFourAP_3673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 388408415123) ^ 194204207561 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 388408415123) ^ 55486916446 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 388408415123) ^ 29877570394 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 388408415123) ^ 810873518 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 388408415123) ^ 320204794 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 388408415123) ^ 105746914 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_397
      · exact prime_fortyFourAP_2531
      · exact prime_fortyFourAP_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_531914489033 : Nat.Prime 531914489033 := by
  apply lucas_primality 531914489033 (3 : ZMod 531914489033)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (157, 1), (557, 1), (760321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (157, 1), (557, 1), (760321, 1)] : List FactorBlock).map factorBlockValue).prod) = 531914489033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_157
      · exact prime_fortyFourAP_557
      · exact prime_fortyFourAP_760321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 531914489033) ^ 265957244516 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 531914489033) ^ 3387990376 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 531914489033) ^ 954963176 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 531914489033) ^ 699592 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_756321939917 : Nat.Prime 756321939917 := by
  apply lucas_primality 756321939917 (2 : ZMod 756321939917)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (18077, 1), (10459727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (18077, 1), (10459727, 1)] : List FactorBlock).map factorBlockValue).prod) = 756321939917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_18077
      · exact prime_fortyFourAP_10459727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 756321939917) ^ 378160969958 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 756321939917) ^ 41838908 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 756321939917) ^ 72308 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_811224881569 : Nat.Prime 811224881569 := by
  apply lucas_primality 811224881569 (13 : ZMod 811224881569)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (938917687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (938917687, 1)] : List FactorBlock).map factorBlockValue).prod) = 811224881569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_938917687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 811224881569) ^ 405612440784 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 811224881569) ^ 270408293856 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 811224881569) ^ 864 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1022269722017 : Nat.Prime 1022269722017 := by
  apply lucas_primality 1022269722017 (3 : ZMod 1022269722017)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (31945928813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (31945928813, 1)] : List FactorBlock).map factorBlockValue).prod) = 1022269722017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_31945928813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1022269722017) ^ 511134861008 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1022269722017) ^ 32 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1143045681439 : Nat.Prime 1143045681439 := by
  apply lucas_primality 1143045681439 (6 : ZMod 1143045681439)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (190507613573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (190507613573, 1)] : List FactorBlock).map factorBlockValue).prod) = 1143045681439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_190507613573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1143045681439) ^ 571522840719 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143045681439) ^ 381015227146 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143045681439) ^ 6 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1263353313671 : Nat.Prime 1263353313671 := by
  apply lucas_primality 1263353313671 (7 : ZMod 1263353313671)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (18047904481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (18047904481, 1)] : List FactorBlock).map factorBlockValue).prod) = 1263353313671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_18047904481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1263353313671) ^ 631676656835 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1263353313671) ^ 252670662734 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1263353313671) ^ 180479044810 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1263353313671) ^ 70 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1327893142907 : Nat.Prime 1327893142907 := by
  apply lucas_primality 1327893142907 (2 : ZMod 1327893142907)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (53, 1), (1138844891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (53, 1), (1138844891, 1)] : List FactorBlock).map factorBlockValue).prod) = 1327893142907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_53
      · exact prime_fortyFourAP_1138844891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1327893142907) ^ 663946571453 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1327893142907) ^ 120717558446 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1327893142907) ^ 25054587602 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1327893142907) ^ 1166 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_35279
      · exact prime_fortyFourAP_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1987018880687 : Nat.Prime 1987018880687 := by
  apply lucas_primality 1987018880687 (5 : ZMod 1987018880687)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (141929920049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (141929920049, 1)] : List FactorBlock).map factorBlockValue).prod) = 1987018880687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_141929920049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1987018880687) ^ 993509440343 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1987018880687) ^ 283859840098 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1987018880687) ^ 14 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2238205449829 : Nat.Prime 2238205449829 := by
  apply lucas_primality 2238205449829 (2 : ZMod 2238205449829)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (947, 1), (3907, 1), (50411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (947, 1), (3907, 1), (50411, 1)] : List FactorBlock).map factorBlockValue).prod) = 2238205449829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_947
      · exact prime_fortyFourAP_3907
      · exact prime_fortyFourAP_50411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2238205449829) ^ 1119102724914 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2238205449829) ^ 746068483276 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2238205449829) ^ 2363469324 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2238205449829) ^ 572870604 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2238205449829) ^ 44399148 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2340867574039 : Nat.Prime 2340867574039 := by
  apply lucas_primality 2340867574039 (3 : ZMod 2340867574039)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (174157, 1), (320027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (174157, 1), (320027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2340867574039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_174157
      · exact prime_fortyFourAP_320027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2340867574039) ^ 1170433787019 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2340867574039) ^ 780289191346 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2340867574039) ^ 334409653434 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2340867574039) ^ 13441134 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2340867574039) ^ 7314594 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2534037753277 : Nat.Prime 2534037753277 := by
  apply lucas_primality 2534037753277 (2 : ZMod 2534037753277)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (379, 1), (185725429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (379, 1), (185725429, 1)] : List FactorBlock).map factorBlockValue).prod) = 2534037753277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_379
      · exact prime_fortyFourAP_185725429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2534037753277) ^ 1267018876638 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2534037753277) ^ 844679251092 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2534037753277) ^ 6686115444 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2534037753277) ^ 13644 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2796680117807 : Nat.Prime 2796680117807 := by
  apply lucas_primality 2796680117807 (5 : ZMod 2796680117807)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (157, 1), (593, 1), (246223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (157, 1), (593, 1), (246223, 1)] : List FactorBlock).map factorBlockValue).prod) = 2796680117807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_61
      · exact prime_fortyFourAP_157
      · exact prime_fortyFourAP_593
      · exact prime_fortyFourAP_246223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2796680117807) ^ 1398340058903 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2796680117807) ^ 45847215046 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2796680117807) ^ 17813249158 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2796680117807) ^ 4716155342 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2796680117807) ^ 11358322 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2909674311721 : Nat.Prime 2909674311721 := by
  apply lucas_primality 2909674311721 (13 : ZMod 2909674311721)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (191, 1), (11540831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (191, 1), (11540831, 1)] : List FactorBlock).map factorBlockValue).prod) = 2909674311721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_191
      · exact prime_fortyFourAP_11540831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2909674311721) ^ 1454837155860 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 969891437240 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 581934862344 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 264515846520 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 15233896920 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 252120 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_3496992739049 : Nat.Prime 3496992739049 := by
  apply lucas_primality 3496992739049 (3 : ZMod 3496992739049)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (103, 1), (98695889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (103, 1), (98695889, 1)] : List FactorBlock).map factorBlockValue).prod) = 3496992739049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_43
      · exact prime_fortyFourAP_103
      · exact prime_fortyFourAP_98695889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3496992739049) ^ 1748496369524 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3496992739049) ^ 81325412536 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3496992739049) ^ 33951385816 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3496992739049) ^ 35432 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_3850926034597 : Nat.Prime 3850926034597 := by
  apply lucas_primality 3850926034597 (5 : ZMod 3850926034597)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (83, 1), (3866391601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (83, 1), (3866391601, 1)] : List FactorBlock).map factorBlockValue).prod) = 3850926034597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_83
      · exact prime_fortyFourAP_3866391601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3850926034597) ^ 1925463017298 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3850926034597) ^ 1283642011532 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3850926034597) ^ 46396699212 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3850926034597) ^ 996 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_4446557982871 : Nat.Prime 4446557982871 := by
  apply lucas_primality 4446557982871 (3 : ZMod 4446557982871)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (73, 1), (1381, 1), (1470233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (73, 1), (1381, 1), (1470233, 1)] : List FactorBlock).map factorBlockValue).prod) = 4446557982871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_73
      · exact prime_fortyFourAP_1381
      · exact prime_fortyFourAP_1470233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4446557982871) ^ 2223278991435 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4446557982871) ^ 1482185994290 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4446557982871) ^ 889311596574 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4446557982871) ^ 60911753190 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4446557982871) ^ 3219810270 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4446557982871) ^ 3024390 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_4819414370321 : Nat.Prime 4819414370321 := by
  apply lucas_primality 4819414370321 (3 : ZMod 4819414370321)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 1), (17, 1), (2081, 1), (154807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 1), (17, 1), (2081, 1), (154807, 1)] : List FactorBlock).map factorBlockValue).prod) = 4819414370321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_2081
      · exact prime_fortyFourAP_154807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4819414370321) ^ 2409707185160 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 963882874064 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 438128579120 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 283494962960 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 2315912720 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 31131760 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_5272876883773 : Nat.Prime 5272876883773 := by
  apply lucas_primality 5272876883773 (2 : ZMod 5272876883773)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (19, 1), (61, 1), (769, 1), (54779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (19, 1), (61, 1), (769, 1), (54779, 1)] : List FactorBlock).map factorBlockValue).prod) = 5272876883773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_61
      · exact prime_fortyFourAP_769
      · exact prime_fortyFourAP_54779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5272876883773) ^ 2636438441886 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5272876883773) ^ 1757625627924 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5272876883773) ^ 277519835988 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5272876883773) ^ 86440604652 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5272876883773) ^ 6856796988 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5272876883773) ^ 96257268 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_5648096221913 : Nat.Prime 5648096221913 := by
  apply lucas_primality 5648096221913 (3 : ZMod 5648096221913)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37799, 1), (18678061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37799, 1), (18678061, 1)] : List FactorBlock).map factorBlockValue).prod) = 5648096221913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_37799
      · exact prime_fortyFourAP_18678061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5648096221913) ^ 2824048110956 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5648096221913) ^ 149424488 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5648096221913) ^ 302392 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_5844250980341 : Nat.Prime 5844250980341 := by
  apply lucas_primality 5844250980341 (2 : ZMod 5844250980341)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (103, 1), (149316581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (103, 1), (149316581, 1)] : List FactorBlock).map factorBlockValue).prod) = 5844250980341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_103
      · exact prime_fortyFourAP_149316581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5844250980341) ^ 2922125490170 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5844250980341) ^ 1168850196068 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5844250980341) ^ 307592156860 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5844250980341) ^ 56740300780 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5844250980341) ^ 39140 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_6549753562109 : Nat.Prime 6549753562109 := by
  apply lucas_primality 6549753562109 (2 : ZMod 6549753562109)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1667, 1), (982266581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1667, 1), (982266581, 1)] : List FactorBlock).map factorBlockValue).prod) = 6549753562109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_1667
      · exact prime_fortyFourAP_982266581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6549753562109) ^ 3274876781054 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6549753562109) ^ 3929066324 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6549753562109) ^ 6668 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_8178157776137 : Nat.Prime 8178157776137 := by
  apply lucas_primality 8178157776137 (3 : ZMod 8178157776137)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1022269722017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1022269722017, 1)] : List FactorBlock).map factorBlockValue).prod) = 8178157776137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_1022269722017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 8178157776137) ^ 4089078888068 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8178157776137) ^ 8 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_8408692477489 : Nat.Prime 8408692477489 := by
  apply lucas_primality 8408692477489 (13 : ZMod 8408692477489)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (571, 1), (18046883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (571, 1), (18046883, 1)] : List FactorBlock).map factorBlockValue).prod) = 8408692477489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_571
      · exact prime_fortyFourAP_18046883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 8408692477489) ^ 4204346238744 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 8408692477489) ^ 2802897492496 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 8408692477489) ^ 494628969264 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 8408692477489) ^ 14726256528 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 8408692477489) ^ 465936 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_8939337443089 : Nat.Prime 8939337443089 := by
  apply lucas_primality 8939337443089 (29 : ZMod 8939337443089)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (14325861287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (14325861287, 1)] : List FactorBlock).map factorBlockValue).prod) = 8939337443089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_14325861287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 8939337443089) ^ 4469668721544 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (29 : ZMod 8939337443089) ^ 2979779147696 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (29 : ZMod 8939337443089) ^ 687641341776 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (29 : ZMod 8939337443089) ^ 624 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_10090602355369 : Nat.Prime 10090602355369 := by
  apply lucas_primality 10090602355369 (11 : ZMod 10090602355369)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (67, 1), (263, 1), (1201, 1), (19867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (67, 1), (263, 1), (1201, 1), (19867, 1)] : List FactorBlock).map factorBlockValue).prod) = 10090602355369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_67
      · exact prime_fortyFourAP_263
      · exact prime_fortyFourAP_1201
      · exact prime_fortyFourAP_19867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 10090602355369) ^ 5045301177684 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 10090602355369) ^ 3363534118456 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 10090602355369) ^ 150606005304 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 10090602355369) ^ 38367309336 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 10090602355369) ^ 8401833768 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 10090602355369) ^ 507907704 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_12146595562733 : Nat.Prime 12146595562733 := by
  apply lucas_primality 12146595562733 (2 : ZMod 12146595562733)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (21846394897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (21846394897, 1)] : List FactorBlock).map factorBlockValue).prod) = 12146595562733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_139
      · exact prime_fortyFourAP_21846394897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12146595562733) ^ 6073297781366 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 12146595562733) ^ 87385579588 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 12146595562733) ^ 556 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_14719672578593 : Nat.Prime 14719672578593 := by
  apply lucas_primality 14719672578593 (3 : ZMod 14719672578593)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (43, 1), (10697436467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (43, 1), (10697436467, 1)] : List FactorBlock).map factorBlockValue).prod) = 14719672578593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_43
      · exact prime_fortyFourAP_10697436467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 14719672578593) ^ 7359836289296 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 14719672578593) ^ 342317966944 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 14719672578593) ^ 1376 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_25856708474741 : Nat.Prime 25856708474741 := by
  apply lucas_primality 25856708474741 (2 : ZMod 25856708474741)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (13, 1), (29, 1), (113, 1), (1291, 1), (2137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (13, 1), (29, 1), (113, 1), (1291, 1), (2137, 1)] : List FactorBlock).map factorBlockValue).prod) = 25856708474741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_113
      · exact prime_fortyFourAP_1291
      · exact prime_fortyFourAP_2137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25856708474741) ^ 12928354237370 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 25856708474741) ^ 5171341694948 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 25856708474741) ^ 2350609861340 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 25856708474741) ^ 1988977574980 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 25856708474741) ^ 891610637060 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 25856708474741) ^ 228820428980 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 25856708474741) ^ 20028434140 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 25856708474741) ^ 12099536020 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_56020723162777 : Nat.Prime 56020723162777 := by
  apply lucas_primality 56020723162777 (5 : ZMod 56020723162777)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (271, 1), (2871090773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (271, 1), (2871090773, 1)] : List FactorBlock).map factorBlockValue).prod) = 56020723162777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_271
      · exact prime_fortyFourAP_2871090773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 56020723162777) ^ 28010361581388 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 56020723162777) ^ 18673574387592 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 56020723162777) ^ 206718535656 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 56020723162777) ^ 19512 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_60421700572451 : Nat.Prime 60421700572451 := by
  apply lucas_primality 60421700572451 (2 : ZMod 60421700572451)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod) = 60421700572451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_89
      · exact prime_fortyFourAP_277100209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60421700572451) ^ 30210850286225 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 12084340114490 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 8631671510350 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 678895512050 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 218050 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_63213296833747 : Nat.Prime 63213296833747 := by
  apply lucas_primality 63213296833747 (2 : ZMod 63213296833747)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (558863, 1), (6283919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (558863, 1), (6283919, 1)] : List FactorBlock).map factorBlockValue).prod) = 63213296833747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_558863
      · exact prime_fortyFourAP_6283919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 63213296833747) ^ 31606648416873 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 63213296833747) ^ 21071098944582 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 63213296833747) ^ 113110542 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 63213296833747) ^ 10059534 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_110784210377741 : Nat.Prime 110784210377741 := by
  apply lucas_primality 110784210377741 (7 : ZMod 110784210377741)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19841, 1), (279180007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19841, 1), (279180007, 1)] : List FactorBlock).map factorBlockValue).prod) = 110784210377741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_19841
      · exact prime_fortyFourAP_279180007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 110784210377741) ^ 55392105188870 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 110784210377741) ^ 22156842075548 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 110784210377741) ^ 5583600140 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 110784210377741) ^ 396820 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_141694423304297 : Nat.Prime 141694423304297 := by
  apply lucas_primality 141694423304297 (3 : ZMod 141694423304297)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (9241, 1), (26833, 1), (71429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (9241, 1), (26833, 1), (71429, 1)] : List FactorBlock).map factorBlockValue).prod) = 141694423304297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_9241
      · exact prime_fortyFourAP_26833
      · exact prime_fortyFourAP_71429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 141694423304297) ^ 70847211652148 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 141694423304297) ^ 15333234856 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 141694423304297) ^ 5280603112 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 141694423304297) ^ 1983710024 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_145979091766243 : Nat.Prime 145979091766243 := by
  apply lucas_primality 145979091766243 (2 : ZMod 145979091766243)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (47, 1), (24650302561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (47, 1), (24650302561, 1)] : List FactorBlock).map factorBlockValue).prod) = 145979091766243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_24650302561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 145979091766243) ^ 72989545883121 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 145979091766243) ^ 48659697255414 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 145979091766243) ^ 20854155966606 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 145979091766243) ^ 3105938122686 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 145979091766243) ^ 5922 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_269887204737977 : Nat.Prime 269887204737977 := by
  apply lucas_primality 269887204737977 (3 : ZMod 269887204737977)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (4819414370321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (4819414370321, 1)] : List FactorBlock).map factorBlockValue).prod) = 269887204737977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_4819414370321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 269887204737977) ^ 134943602368988 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 269887204737977) ^ 38555314962568 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 269887204737977) ^ 56 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_323387170734367 : Nat.Prime 323387170734367 := by
  apply lucas_primality 323387170734367 (3 : ZMod 323387170734367)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (773, 1), (23241855019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (773, 1), (23241855019, 1)] : List FactorBlock).map factorBlockValue).prod) = 323387170734367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_773
      · exact prime_fortyFourAP_23241855019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 323387170734367) ^ 161693585367183 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 323387170734367) ^ 107795723578122 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 323387170734367) ^ 418353390342 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 323387170734367) ^ 13914 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_662206480715413 : Nat.Prime 662206480715413 := by
  apply lucas_primality 662206480715413 (11 : ZMod 662206480715413)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (565589, 1), (32522953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (565589, 1), (32522953, 1)] : List FactorBlock).map factorBlockValue).prod) = 662206480715413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_565589
      · exact prime_fortyFourAP_32522953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 662206480715413) ^ 331103240357706 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 662206480715413) ^ 220735493571804 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 662206480715413) ^ 1170826308 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (11 : ZMod 662206480715413) ^ 20361204 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_758887183004437 : Nat.Prime 758887183004437 := by
  apply lucas_primality 758887183004437 (5 : ZMod 758887183004437)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (19, 1), (61, 1), (673639457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (19, 1), (61, 1), (673639457, 1)] : List FactorBlock).map factorBlockValue).prod) = 758887183004437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_61
      · exact prime_fortyFourAP_673639457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 758887183004437) ^ 379443591502218 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 758887183004437) ^ 252962394334812 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 758887183004437) ^ 39941430684444 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 758887183004437) ^ 12440773491876 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 758887183004437) ^ 1126548 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_975024484924757 : Nat.Prime 975024484924757 := by
  apply lucas_primality 975024484924757 (2 : ZMod 975024484924757)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (23, 1), (349529, 1), (4331581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (23, 1), (349529, 1), (4331581, 1)] : List FactorBlock).map factorBlockValue).prod) = 975024484924757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_23
      · exact prime_fortyFourAP_349529
      · exact prime_fortyFourAP_4331581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 975024484924757) ^ 487512242462378 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 975024484924757) ^ 139289212132108 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 975024484924757) ^ 42392368909772 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 975024484924757) ^ 2789538164 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 975024484924757) ^ 225096676 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1012564812501629 : Nat.Prime 1012564812501629 := by
  apply lucas_primality 1012564812501629 (2 : ZMod 1012564812501629)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1883407, 1), (134406001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1883407, 1), (134406001, 1)] : List FactorBlock).map factorBlockValue).prod) = 1012564812501629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_1883407
      · exact prime_fortyFourAP_134406001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1012564812501629) ^ 506282406250814 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1012564812501629) ^ 537624004 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1012564812501629) ^ 7533628 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1132865085569267 : Nat.Prime 1132865085569267 := by
  apply lucas_primality 1132865085569267 (2 : ZMod 1132865085569267)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (223, 1), (362865177953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (223, 1), (362865177953, 1)] : List FactorBlock).map factorBlockValue).prod) = 1132865085569267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_223
      · exact prime_fortyFourAP_362865177953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1132865085569267) ^ 566432542784633 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1132865085569267) ^ 161837869367038 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1132865085569267) ^ 5080112491342 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1132865085569267) ^ 3122 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1384711894151563 : Nat.Prime 1384711894151563 := by
  apply lucas_primality 1384711894151563 (2 : ZMod 1384711894151563)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (12146595562733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (12146595562733, 1)] : List FactorBlock).map factorBlockValue).prod) = 1384711894151563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_12146595562733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1384711894151563) ^ 692355947075781 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1384711894151563) ^ 461570631383854 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1384711894151563) ^ 72879573376398 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1384711894151563) ^ 114 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_41
      · exact prime_fortyFourAP_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1940323024406203 : Nat.Prime 1940323024406203 := by
  apply lucas_primality 1940323024406203 (2 : ZMod 1940323024406203)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (323387170734367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (323387170734367, 1)] : List FactorBlock).map factorBlockValue).prod) = 1940323024406203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_323387170734367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1940323024406203) ^ 970161512203101 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1940323024406203) ^ 646774341468734 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1940323024406203) ^ 6 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2987736414979633 : Nat.Prime 2987736414979633 := by
  apply lucas_primality 2987736414979633 (10 : ZMod 2987736414979633)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (23, 1), (41, 1), (229, 1), (15170513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (23, 1), (41, 1), (229, 1), (15170513, 1)] : List FactorBlock).map factorBlockValue).prod) = 2987736414979633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_23
      · exact prime_fortyFourAP_41
      · exact prime_fortyFourAP_229
      · exact prime_fortyFourAP_15170513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2987736414979633) ^ 1493868207489816 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 2987736414979633) ^ 995912138326544 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 2987736414979633) ^ 157249284998928 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 2987736414979633) ^ 129901583259984 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 2987736414979633) ^ 72871619877552 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 2987736414979633) ^ 13046883908208 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 2987736414979633) ^ 196943664 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_3764154169391339 : Nat.Prime 3764154169391339 := by
  apply lucas_primality 3764154169391339 (2 : ZMod 3764154169391339)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (839, 1), (36774401311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (839, 1), (36774401311, 1)] : List FactorBlock).map factorBlockValue).prod) = 3764154169391339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_61
      · exact prime_fortyFourAP_839
      · exact prime_fortyFourAP_36774401311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3764154169391339) ^ 1882077084695669 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3764154169391339) ^ 61707445399858 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3764154169391339) ^ 4486476959942 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3764154169391339) ^ 102358 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_5878517680718509 : Nat.Prime 5878517680718509 := by
  apply lucas_primality 5878517680718509 (2 : ZMod 5878517680718509)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (17, 1), (22193, 1), (26498761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (17, 1), (22193, 1), (26498761, 1)] : List FactorBlock).map factorBlockValue).prod) = 5878517680718509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_22193
      · exact prime_fortyFourAP_26498761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5878517680718509) ^ 2939258840359254 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5878517680718509) ^ 1959505893572836 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5878517680718509) ^ 839788240102644 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5878517680718509) ^ 345795157689324 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5878517680718509) ^ 264881614956 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5878517680718509) ^ 221841228 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_8899091597863531 : Nat.Prime 8899091597863531 := by
  apply lucas_primality 8899091597863531 (2 : ZMod 8899091597863531)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (661, 1), (2311, 1), (2887, 1), (3203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (661, 1), (2311, 1), (2887, 1), (3203, 1)] : List FactorBlock).map factorBlockValue).prod) = 8899091597863531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_661
      · exact prime_fortyFourAP_2311
      · exact prime_fortyFourAP_2887
      · exact prime_fortyFourAP_3203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8899091597863531) ^ 4449545798931765 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8899091597863531) ^ 2966363865954510 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8899091597863531) ^ 1779818319572706 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8899091597863531) ^ 1271298799694790 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8899091597863531) ^ 13463073521730 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8899091597863531) ^ 3850753612230 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8899091597863531) ^ 3082470245190 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8899091597863531) ^ 2778361410510 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_8901011109124019 : Nat.Prime 8901011109124019 := by
  apply lucas_primality 8901011109124019 (2 : ZMod 8901011109124019)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (32804257, 1), (135668537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (32804257, 1), (135668537, 1)] : List FactorBlock).map factorBlockValue).prod) = 8901011109124019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_32804257
      · exact prime_fortyFourAP_135668537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8901011109124019) ^ 4450505554562009 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8901011109124019) ^ 271337074 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8901011109124019) ^ 65608514 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_10279120799235109 : Nat.Prime 10279120799235109 := by
  apply lucas_primality 10279120799235109 (6 : ZMod 10279120799235109)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (347, 1), (827, 1), (28687, 1), (104053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (347, 1), (827, 1), (28687, 1), (104053, 1)] : List FactorBlock).map factorBlockValue).prod) = 10279120799235109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_347
      · exact prime_fortyFourAP_827
      · exact prime_fortyFourAP_28687
      · exact prime_fortyFourAP_104053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10279120799235109) ^ 5139560399617554 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 3426373599745036 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 29622826510764 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 12429408463404 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 358319824284 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 98787356436 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_13745226048974351 : Nat.Prime 13745226048974351 := by
  apply lucas_primality 13745226048974351 (14 : ZMod 13745226048974351)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (23, 1), (61, 1), (35797, 1), (781951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (23, 1), (61, 1), (35797, 1), (781951, 1)] : List FactorBlock).map factorBlockValue).prod) = 13745226048974351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_23
      · exact prime_fortyFourAP_61
      · exact prime_fortyFourAP_35797
      · exact prime_fortyFourAP_781951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 13745226048974351) ^ 6872613024487175 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (14 : ZMod 13745226048974351) ^ 2749045209794870 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (14 : ZMod 13745226048974351) ^ 1963603721282050 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (14 : ZMod 13745226048974351) ^ 597618523868450 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (14 : ZMod 13745226048974351) ^ 225331574573350 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (14 : ZMod 13745226048974351) ^ 383977038550 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (14 : ZMod 13745226048974351) ^ 17578116850 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_20000838920189041 : Nat.Prime 20000838920189041 := by
  apply lucas_primality 20000838920189041 (7 : ZMod 20000838920189041)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod) = 20000838920189041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_384973
      · exact prime_fortyFourAP_72158159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20000838920189041) ^ 10000419460094520 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 6666946306729680 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 4000167784037808 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 51953874480 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 277180560 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_30492110377557209 : Nat.Prime 30492110377557209 := by
  apply lucas_primality 30492110377557209 (3 : ZMod 30492110377557209)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (1637, 1), (6529, 1), (11503777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (1637, 1), (6529, 1), (11503777, 1)] : List FactorBlock).map factorBlockValue).prod) = 30492110377557209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_31
      · exact prime_fortyFourAP_1637
      · exact prime_fortyFourAP_6529
      · exact prime_fortyFourAP_11503777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30492110377557209) ^ 15246055188778604 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 30492110377557209) ^ 983616463792168 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 30492110377557209) ^ 18626823688184 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 30492110377557209) ^ 4670257371352 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 30492110377557209) ^ 2650617304 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_46093020050440787 : Nat.Prime 46093020050440787 := by
  apply lucas_primality 46093020050440787 (2 : ZMod 46093020050440787)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (73, 1), (4446557982871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (73, 1), (4446557982871, 1)] : List FactorBlock).map factorBlockValue).prod) = 46093020050440787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_71
      · exact prime_fortyFourAP_73
      · exact prime_fortyFourAP_4446557982871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46093020050440787) ^ 23046510025220393 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46093020050440787) ^ 649197465499166 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46093020050440787) ^ 631411233567682 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46093020050440787) ^ 10366 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_46850588275089773 : Nat.Prime 46850588275089773 := by
  apply lucas_primality 46850588275089773 (2 : ZMod 46850588275089773)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (157, 1), (3011, 1), (313629971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (157, 1), (3011, 1), (313629971, 1)] : List FactorBlock).map factorBlockValue).prod) = 46850588275089773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_79
      · exact prime_fortyFourAP_157
      · exact prime_fortyFourAP_3011
      · exact prime_fortyFourAP_313629971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 46850588275089773) ^ 23425294137544886 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46850588275089773) ^ 593045421203668 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46850588275089773) ^ 298411390287196 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46850588275089773) ^ 15559810121252 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46850588275089773) ^ 149381732 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_89292073564459247 : Nat.Prime 89292073564459247 := by
  apply lucas_primality 89292073564459247 (5 : ZMod 89292073564459247)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (31, 1), (110784210377741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (31, 1), (110784210377741, 1)] : List FactorBlock).map factorBlockValue).prod) = 89292073564459247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_31
      · exact prime_fortyFourAP_110784210377741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 89292073564459247) ^ 44646036782229623 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 89292073564459247) ^ 6868621043419942 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 89292073564459247) ^ 2880389469821266 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 89292073564459247) ^ 806 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_140392491357773839 : Nat.Prime 140392491357773839 := by
  apply lucas_primality 140392491357773839 (6 : ZMod 140392491357773839)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (1559, 1), (14423, 1), (22140787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (1559, 1), (14423, 1), (22140787, 1)] : List FactorBlock).map factorBlockValue).prod) = 140392491357773839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_1559
      · exact prime_fortyFourAP_14423
      · exact prime_fortyFourAP_22140787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 140392491357773839) ^ 70196245678886919 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392491357773839) ^ 46797497119257946 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392491357773839) ^ 2987074284207954 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392491357773839) ^ 90052912994082 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392491357773839) ^ 9733931315106 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392491357773839) ^ 6340898874 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_169369845948702271 : Nat.Prime 169369845948702271 := by
  apply lucas_primality 169369845948702271 (6 : ZMod 169369845948702271)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (47, 1), (61, 1), (1723, 1), (380961083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (47, 1), (61, 1), (1723, 1), (380961083, 1)] : List FactorBlock).map factorBlockValue).prod) = 169369845948702271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_61
      · exact prime_fortyFourAP_1723
      · exact prime_fortyFourAP_380961083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 169369845948702271) ^ 84684922974351135 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 169369845948702271) ^ 56456615316234090 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 169369845948702271) ^ 33873969189740454 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 169369845948702271) ^ 3603613743589410 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 169369845948702271) ^ 2776554851618070 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 169369845948702271) ^ 98299388246490 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 169369845948702271) ^ 444585690 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_263505991609941173 : Nat.Prime 263505991609941173 := by
  apply lucas_primality 263505991609941173 (2 : ZMod 263505991609941173)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (11068193, 1), (61359533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (11068193, 1), (61359533, 1)] : List FactorBlock).map factorBlockValue).prod) = 263505991609941173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_97
      · exact prime_fortyFourAP_11068193
      · exact prime_fortyFourAP_61359533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 263505991609941173) ^ 131752995804970586 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 263505991609941173) ^ 2716556614535476 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 263505991609941173) ^ 23807498804 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 263505991609941173) ^ 4294458884 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_374376818878815937 : Nat.Prime 374376818878815937 := by
  apply lucas_primality 374376818878815937 (5 : ZMod 374376818878815937)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (35569, 1), (54819625657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (35569, 1), (54819625657, 1)] : List FactorBlock).map factorBlockValue).prod) = 374376818878815937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_35569
      · exact prime_fortyFourAP_54819625657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 374376818878815937) ^ 187188409439407968 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 374376818878815937) ^ 124792272959605312 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 374376818878815937) ^ 10525368126144 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 374376818878815937) ^ 6829248 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_409510283668397941 : Nat.Prime 409510283668397941 := by
  apply lucas_primality 409510283668397941 (2 : ZMod 409510283668397941)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (975024484924757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (975024484924757, 1)] : List FactorBlock).map factorBlockValue).prod) = 409510283668397941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_975024484924757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 409510283668397941) ^ 204755141834198970 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 409510283668397941) ^ 136503427889465980 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 409510283668397941) ^ 81902056733679588 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 409510283668397941) ^ 58501469095485420 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 409510283668397941) ^ 420 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_554011756364663489 : Nat.Prime 554011756364663489 := by
  apply lucas_primality 554011756364663489 (3 : ZMod 554011756364663489)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (41, 1), (10691, 1), (19748623057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (41, 1), (10691, 1), (19748623057, 1)] : List FactorBlock).map factorBlockValue).prod) = 554011756364663489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_41
      · exact prime_fortyFourAP_10691
      · exact prime_fortyFourAP_19748623057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 554011756364663489) ^ 277005878182331744 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 554011756364663489) ^ 13512481862552768 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 554011756364663489) ^ 51820386901568 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 554011756364663489) ^ 28053184 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_61717
      · exact prime_fortyFourAP_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_589747084636144349 : Nat.Prime 589747084636144349 := by
  apply lucas_primality 589747084636144349 (2 : ZMod 589747084636144349)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (617, 1), (1427, 1), (84349, 1), (1985257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (617, 1), (1427, 1), (84349, 1), (1985257, 1)] : List FactorBlock).map factorBlockValue).prod) = 589747084636144349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_617
      · exact prime_fortyFourAP_1427
      · exact prime_fortyFourAP_84349
      · exact prime_fortyFourAP_1985257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 589747084636144349) ^ 294873542318072174 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 589747084636144349) ^ 955829958891644 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 589747084636144349) ^ 413277564566324 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 589747084636144349) ^ 6991749571852 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 589747084636144349) ^ 297063344764 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_821350062669399719 : Nat.Prime 821350062669399719 := by
  apply lucas_primality 821350062669399719 (7 : ZMod 821350062669399719)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (28617707, 1), (157696507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (28617707, 1), (157696507, 1)] : List FactorBlock).map factorBlockValue).prod) = 821350062669399719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_28617707
      · exact prime_fortyFourAP_157696507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 821350062669399719) ^ 410675031334699859 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 821350062669399719) ^ 117335723238485674 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 821350062669399719) ^ 63180774051492286 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 821350062669399719) ^ 28700764274 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 821350062669399719) ^ 5208422674 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_826636823185963187 : Nat.Prime 826636823185963187 := by
  apply lucas_primality 826636823185963187 (2 : ZMod 826636823185963187)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (80744533, 1), (5118840821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (80744533, 1), (5118840821, 1)] : List FactorBlock).map factorBlockValue).prod) = 826636823185963187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_80744533
      · exact prime_fortyFourAP_5118840821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 826636823185963187) ^ 413318411592981593 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 826636823185963187) ^ 10237681642 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 826636823185963187) ^ 161489066 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_859806059102301397 : Nat.Prime 859806059102301397 := by
  apply lucas_primality 859806059102301397 (2 : ZMod 859806059102301397)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1279, 1), (56020723162777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1279, 1), (56020723162777, 1)] : List FactorBlock).map factorBlockValue).prod) = 859806059102301397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_1279
      · exact prime_fortyFourAP_56020723162777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 859806059102301397) ^ 429903029551150698 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 859806059102301397) ^ 286602019700767132 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 859806059102301397) ^ 672248677953324 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 859806059102301397) ^ 15348 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_878232026121702859 : Nat.Prime 878232026121702859 := by
  apply lucas_primality 878232026121702859 (2 : ZMod 878232026121702859)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (91432559, 1), (533624659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (91432559, 1), (533624659, 1)] : List FactorBlock).map factorBlockValue).prod) = 878232026121702859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_91432559
      · exact prime_fortyFourAP_533624659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 878232026121702859) ^ 439116013060851429 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 878232026121702859) ^ 292744008707234286 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 878232026121702859) ^ 9605243862 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 878232026121702859) ^ 1645786062 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_966194795839257487 : Nat.Prime 966194795839257487 := by
  apply lucas_primality 966194795839257487 (3 : ZMod 966194795839257487)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (19, 1), (977, 1), (1627, 1), (34848677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (19, 1), (977, 1), (1627, 1), (34848677, 1)] : List FactorBlock).map factorBlockValue).prod) = 966194795839257487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_977
      · exact prime_fortyFourAP_1627
      · exact prime_fortyFourAP_34848677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 966194795839257487) ^ 483097397919628743 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 966194795839257487) ^ 322064931946419162 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 966194795839257487) ^ 56834987990544558 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 966194795839257487) ^ 50852357675750394 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 966194795839257487) ^ 988940425628718 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 966194795839257487) ^ 593850519876618 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 966194795839257487) ^ 27725436918 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_974357259695558663 : Nat.Prime 974357259695558663 := by
  apply lucas_primality 974357259695558663 (5 : ZMod 974357259695558663)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (11, 1), (18217, 1), (7088013991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (11, 1), (18217, 1), (7088013991, 1)] : List FactorBlock).map factorBlockValue).prod) = 974357259695558663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_18217
      · exact prime_fortyFourAP_7088013991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 974357259695558663) ^ 487178629847779331 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 974357259695558663) ^ 139193894242222666 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 974357259695558663) ^ 88577932699596242 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 974357259695558663) ^ 53486153576086 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 974357259695558663) ^ 137465482 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_982070368610347837 : Nat.Prime 982070368610347837 := by
  apply lucas_primality 982070368610347837 (2 : ZMod 982070368610347837)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (251, 1), (16349, 1), (738639761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (251, 1), (16349, 1), (738639761, 1)] : List FactorBlock).map factorBlockValue).prod) = 982070368610347837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_251
      · exact prime_fortyFourAP_16349
      · exact prime_fortyFourAP_738639761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 982070368610347837) ^ 491035184305173918 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 982070368610347837) ^ 327356789536782612 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 982070368610347837) ^ 3912630950638836 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 982070368610347837) ^ 60069139923564 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 982070368610347837) ^ 1329566076 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2143009765547021929 : Nat.Prime 2143009765547021929 := by
  apply lucas_primality 2143009765547021929 (7 : ZMod 2143009765547021929)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (89292073564459247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (89292073564459247, 1)] : List FactorBlock).map factorBlockValue).prod) = 2143009765547021929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_89292073564459247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2143009765547021929) ^ 1071504882773510964 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2143009765547021929) ^ 714336588515673976 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2143009765547021929) ^ 24 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_4497349976643679853 : Nat.Prime 4497349976643679853 := by
  apply lucas_primality 4497349976643679853 (2 : ZMod 4497349976643679853)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (5339791, 1), (2170704469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (5339791, 1), (2170704469, 1)] : List FactorBlock).map factorBlockValue).prod) = 4497349976643679853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_97
      · exact prime_fortyFourAP_5339791
      · exact prime_fortyFourAP_2170704469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4497349976643679853) ^ 2248674988321839926 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4497349976643679853) ^ 46364432748903916 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4497349976643679853) ^ 842233333972 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4497349976643679853) ^ 2071838908 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_4874540587086777007 : Nat.Prime 4874540587086777007 := by
  apply lucas_primality 4874540587086777007 (5 : ZMod 4874540587086777007)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (199, 1), (272887, 1), (204938549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (199, 1), (272887, 1), (204938549, 1)] : List FactorBlock).map factorBlockValue).prod) = 4874540587086777007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_73
      · exact prime_fortyFourAP_199
      · exact prime_fortyFourAP_272887
      · exact prime_fortyFourAP_204938549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4874540587086777007) ^ 2437270293543388503 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4874540587086777007) ^ 1624846862362259002 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4874540587086777007) ^ 66774528590229822 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4874540587086777007) ^ 24495178829581794 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4874540587086777007) ^ 17862853807938 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4874540587086777007) ^ 23785376694 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_4953937646378557129 : Nat.Prime 4953937646378557129 := by
  apply lucas_primality 4953937646378557129 (7 : ZMod 4953937646378557129)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2339, 1), (3329, 1), (26509117937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2339, 1), (3329, 1), (26509117937, 1)] : List FactorBlock).map factorBlockValue).prod) = 4953937646378557129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_2339
      · exact prime_fortyFourAP_3329
      · exact prime_fortyFourAP_26509117937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4953937646378557129) ^ 2476968823189278564 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 4953937646378557129) ^ 1651312548792852376 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 4953937646378557129) ^ 2117972486694552 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 4953937646378557129) ^ 1488115844511432 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (7 : ZMod 4953937646378557129) ^ 186876744 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_439
      · exact prime_fortyFourAP_853
      · exact prime_fortyFourAP_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_18788050697403655777 : Nat.Prime 18788050697403655777 := by
  apply lucas_primality 18788050697403655777 (10 : ZMod 18788050697403655777)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (139, 1), (419, 1), (1129, 1), (2976375529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (139, 1), (419, 1), (1129, 1), (2976375529, 1)] : List FactorBlock).map factorBlockValue).prod) = 18788050697403655777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_139
      · exact prime_fortyFourAP_419
      · exact prime_fortyFourAP_1129
      · exact prime_fortyFourAP_2976375529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 18788050697403655777) ^ 9394025348701827888 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 18788050697403655777) ^ 6262683565801218592 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 18788050697403655777) ^ 135165832355421984 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 18788050697403655777) ^ 44840216461583904 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 18788050697403655777) ^ 16641320369710944 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 18788050697403655777) ^ 6312392544 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_23213589616558142251 : Nat.Prime 23213589616558142251 := by
  apply lucas_primality 23213589616558142251 (3 : ZMod 23213589616558142251)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (14813, 1), (89759, 1), (23278769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (14813, 1), (89759, 1), (23278769, 1)] : List FactorBlock).map factorBlockValue).prod) = 23213589616558142251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_14813
      · exact prime_fortyFourAP_89759
      · exact prime_fortyFourAP_23278769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23213589616558142251) ^ 11606794808279071125 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 23213589616558142251) ^ 7737863205519380750 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 23213589616558142251) ^ 4642717923311628450 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 23213589616558142251) ^ 1567109270003250 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 23213589616558142251) ^ 258621303897750 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 23213589616558142251) ^ 997200050250 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_28418646871883318789 : Nat.Prime 28418646871883318789 := by
  apply lucas_primality 28418646871883318789 (2 : ZMod 28418646871883318789)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (233, 1), (30492110377557209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (233, 1), (30492110377557209, 1)] : List FactorBlock).map factorBlockValue).prod) = 28418646871883318789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_233
      · exact prime_fortyFourAP_30492110377557209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 28418646871883318789) ^ 14209323435941659394 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 28418646871883318789) ^ 121968441510228836 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 28418646871883318789) ^ 932 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_37134887616756554077 : Nat.Prime 37134887616756554077 := by
  apply lucas_primality 37134887616756554077 (6 : ZMod 37134887616756554077)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (776813, 1), (1327893142907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (776813, 1), (1327893142907, 1)] : List FactorBlock).map factorBlockValue).prod) = 37134887616756554077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_776813
      · exact prime_fortyFourAP_1327893142907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 37134887616756554077) ^ 18567443808378277038 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 37134887616756554077) ^ 12378295872252184692 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 37134887616756554077) ^ 47804153144652 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 37134887616756554077) ^ 27965268 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_57709978139285874797 : Nat.Prime 57709978139285874797 := by
  apply lucas_primality 57709978139285874797 (2 : ZMod 57709978139285874797)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (55379759, 1), (260519272661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (55379759, 1), (260519272661, 1)] : List FactorBlock).map factorBlockValue).prod) = 57709978139285874797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_55379759
      · exact prime_fortyFourAP_260519272661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 57709978139285874797) ^ 28854989069642937398 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 57709978139285874797) ^ 1042077090644 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 57709978139285874797) ^ 221519036 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_110910068172641332811 : Nat.Prime 110910068172641332811 := by
  apply lucas_primality 110910068172641332811 (2 : ZMod 110910068172641332811)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79, 1), (140392491357773839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79, 1), (140392491357773839, 1)] : List FactorBlock).map factorBlockValue).prod) = 110910068172641332811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_79
      · exact prime_fortyFourAP_140392491357773839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 110910068172641332811) ^ 55455034086320666405 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 110910068172641332811) ^ 22182013634528266562 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 110910068172641332811) ^ 1403924913577738390 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 110910068172641332811) ^ 790 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_145849035197483064341 : Nat.Prime 145849035197483064341 := by
  apply lucas_primality 145849035197483064341 (3 : ZMod 145849035197483064341)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (199, 1), (757, 1), (299969, 1), (161379451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (199, 1), (757, 1), (299969, 1), (161379451, 1)] : List FactorBlock).map factorBlockValue).prod) = 145849035197483064341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_199
      · exact prime_fortyFourAP_757
      · exact prime_fortyFourAP_299969
      · exact prime_fortyFourAP_161379451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 145849035197483064341) ^ 72924517598741532170 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 145849035197483064341) ^ 29169807039496612868 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 145849035197483064341) ^ 732909724610467660 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 145849035197483064341) ^ 192667153497335620 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 145849035197483064341) ^ 486213692739860 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 145849035197483064341) ^ 903764601340 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_282723354051033066407 : Nat.Prime 282723354051033066407 := by
  apply lucas_primality 282723354051033066407 (5 : ZMod 282723354051033066407)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (4874540587086777007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (4874540587086777007, 1)] : List FactorBlock).map factorBlockValue).prod) = 282723354051033066407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_4874540587086777007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 282723354051033066407) ^ 141361677025516533203 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 282723354051033066407) ^ 9749081174173554014 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 282723354051033066407) ^ 58 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_364423709151875422649 : Nat.Prime 364423709151875422649 := by
  apply lucas_primality 364423709151875422649 (3 : ZMod 364423709151875422649)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (1381, 1), (1940323024406203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (1381, 1), (1940323024406203, 1)] : List FactorBlock).map factorBlockValue).prod) = 364423709151875422649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_1381
      · exact prime_fortyFourAP_1940323024406203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 364423709151875422649) ^ 182211854575937711324 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 364423709151875422649) ^ 21436688773639730744 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 364423709151875422649) ^ 263883931319243608 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 364423709151875422649) ^ 187816 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_558234740355005780371 : Nat.Prime 558234740355005780371 := by
  apply lucas_primality 558234740355005780371 (2 : ZMod 558234740355005780371)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (5426387, 1), (1143045681439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (5426387, 1), (1143045681439, 1)] : List FactorBlock).map factorBlockValue).prod) = 558234740355005780371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_5426387
      · exact prime_fortyFourAP_1143045681439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 558234740355005780371) ^ 279117370177502890185 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 558234740355005780371) ^ 186078246785001926790 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 558234740355005780371) ^ 111646948071001156074 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 558234740355005780371) ^ 102874111329510 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 558234740355005780371) ^ 488374830 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1113419261968560235841 : Nat.Prime 1113419261968560235841 := by
  apply lucas_primality 1113419261968560235841 (6 : ZMod 1113419261968560235841)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (130021, 1), (2502833, 1), (10692109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (130021, 1), (2502833, 1), (10692109, 1)] : List FactorBlock).map factorBlockValue).prod) = 1113419261968560235841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_130021
      · exact prime_fortyFourAP_2502833
      · exact prime_fortyFourAP_10692109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1113419261968560235841) ^ 556709630984280117920 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1113419261968560235841) ^ 222683852393712047168 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1113419261968560235841) ^ 8563380238335040 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1113419261968560235841) ^ 444863585372480 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1113419261968560235841) ^ 104134671837760 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1213214327206691504111 : Nat.Prime 1213214327206691504111 := by
  apply lucas_primality 1213214327206691504111 (17 : ZMod 1213214327206691504111)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (47, 1), (373297, 1), (531914489033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (47, 1), (373297, 1), (531914489033, 1)] : List FactorBlock).map factorBlockValue).prod) = 1213214327206691504111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_373297
      · exact prime_fortyFourAP_531914489033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1213214327206691504111) ^ 606607163603345752055 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (17 : ZMod 1213214327206691504111) ^ 242642865441338300822 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (17 : ZMod 1213214327206691504111) ^ 93324179015899346470 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (17 : ZMod 1213214327206691504111) ^ 25813070791631734130 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (17 : ZMod 1213214327206691504111) ^ 3249997527991630 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (17 : ZMod 1213214327206691504111) ^ 2280844670 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1843650796088385232153 : Nat.Prime 1843650796088385232153 := by
  apply lucas_primality 1843650796088385232153 (10 : ZMod 1843650796088385232153)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (383, 1), (158761, 1), (1263353313671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (383, 1), (158761, 1), (1263353313671, 1)] : List FactorBlock).map factorBlockValue).prod) = 1843650796088385232153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_383
      · exact prime_fortyFourAP_158761
      · exact prime_fortyFourAP_1263353313671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1843650796088385232153) ^ 921825398044192616076 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 1843650796088385232153) ^ 614550265362795077384 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 1843650796088385232153) ^ 4813709650361319144 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 1843650796088385232153) ^ 11612743659263832 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 1843650796088385232153) ^ 1459331112 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_107
      · exact prime_fortyFourAP_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_3349408442130034682227 : Nat.Prime 3349408442130034682227 := by
  apply lucas_primality 3349408442130034682227 (2 : ZMod 3349408442130034682227)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (558234740355005780371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (558234740355005780371, 1)] : List FactorBlock).map factorBlockValue).prod) = 3349408442130034682227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_558234740355005780371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3349408442130034682227) ^ 1674704221065017341113 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3349408442130034682227) ^ 1116469480710011560742 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3349408442130034682227) ^ 6 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_4430773372276762682321 : Nat.Prime 4430773372276762682321 := by
  apply lucas_primality 4430773372276762682321 (3 : ZMod 4430773372276762682321)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (67, 1), (826636823185963187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (67, 1), (826636823185963187, 1)] : List FactorBlock).map factorBlockValue).prod) = 4430773372276762682321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_67
      · exact prime_fortyFourAP_826636823185963187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4430773372276762682321) ^ 2215386686138381341160 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4430773372276762682321) ^ 886154674455352536464 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4430773372276762682321) ^ 66130945854877054960 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4430773372276762682321) ^ 5360 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_5702520434464066190179 : Nat.Prime 5702520434464066190179 := by
  apply lucas_primality 5702520434464066190179 (2 : ZMod 5702520434464066190179)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (811, 1), (18539, 1), (63213296833747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (811, 1), (18539, 1), (63213296833747, 1)] : List FactorBlock).map factorBlockValue).prod) = 5702520434464066190179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_811
      · exact prime_fortyFourAP_18539
      · exact prime_fortyFourAP_63213296833747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5702520434464066190179) ^ 2851260217232033095089 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5702520434464066190179) ^ 1900840144821355396726 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5702520434464066190179) ^ 7031467860005013798 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5702520434464066190179) ^ 307595902393012902 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5702520434464066190179) ^ 90210774 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_22442462496710053242007 : Nat.Prime 22442462496710053242007 := by
  apply lucas_primality 22442462496710053242007 (5 : ZMod 22442462496710053242007)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (2753, 1), (46850588275089773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (2753, 1), (46850588275089773, 1)] : List FactorBlock).map factorBlockValue).prod) = 22442462496710053242007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_2753
      · exact prime_fortyFourAP_46850588275089773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 22442462496710053242007) ^ 11221231248355026621003 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 22442462496710053242007) ^ 7480820832236684414002 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 22442462496710053242007) ^ 773878017127932870414 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 22442462496710053242007) ^ 8152002359865620502 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 22442462496710053242007) ^ 479022 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_57110078409302094014171 : Nat.Prime 57110078409302094014171 := by
  apply lucas_primality 57110078409302094014171 (6 : ZMod 57110078409302094014171)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (21160721, 1), (269887204737977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (21160721, 1), (269887204737977, 1)] : List FactorBlock).map factorBlockValue).prod) = 57110078409302094014171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_21160721
      · exact prime_fortyFourAP_269887204737977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 57110078409302094014171) ^ 28555039204651047007085 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 57110078409302094014171) ^ 11422015681860418802834 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 57110078409302094014171) ^ 2698872047379770 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (6 : ZMod 57110078409302094014171) ^ 211607210 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_67024695540586320517363 : Nat.Prime 67024695540586320517363 := by
  apply lucas_primality 67024695540586320517363 (3 : ZMod 67024695540586320517363)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (47, 1), (1899647, 1), (2909674311721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (47, 1), (1899647, 1), (2909674311721, 1)] : List FactorBlock).map factorBlockValue).prod) = 67024695540586320517363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_43
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_1899647
      · exact prime_fortyFourAP_2909674311721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 67024695540586320517363) ^ 33512347770293160258681 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 22341565180195440172454 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 1558713849781077221334 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 1426057351927368521646 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 35282710703928846 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 23035119522 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_87853082473754023276453 : Nat.Prime 87853082473754023276453 := by
  apply lucas_primality 87853082473754023276453 (2 : ZMod 87853082473754023276453)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (6076909123, 1), (172105589911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (6076909123, 1), (172105589911, 1)] : List FactorBlock).map factorBlockValue).prod) = 87853082473754023276453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_6076909123
      · exact prime_fortyFourAP_172105589911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 87853082473754023276453) ^ 43926541236877011638226 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 87853082473754023276453) ^ 29284360824584674425484 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 87853082473754023276453) ^ 12550440353393431896636 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 87853082473754023276453) ^ 14456869552524 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 87853082473754023276453) ^ 510460366332 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_212358418450715538616193 : Nat.Prime 212358418450715538616193 := by
  apply lucas_primality 212358418450715538616193 (3 : ZMod 212358418450715538616193)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (1801, 1), (343501679, 1), (2681741641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (1801, 1), (343501679, 1), (2681741641, 1)] : List FactorBlock).map factorBlockValue).prod) = 212358418450715538616193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_1801
      · exact prime_fortyFourAP_343501679
      · exact prime_fortyFourAP_2681741641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 212358418450715538616193) ^ 106179209225357769308096 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 212358418450715538616193) ^ 117911392809947550592 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 212358418450715538616193) ^ 618216537016448 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 212358418450715538616193) ^ 79186755056512 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_614861506554349437030163 : Nat.Prime 614861506554349437030163 := by
  apply lucas_primality 614861506554349437030163 (3 : ZMod 614861506554349437030163)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29304298123, 1), (3496992739049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29304298123, 1), (3496992739049, 1)] : List FactorBlock).map factorBlockValue).prod) = 614861506554349437030163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_29304298123
      · exact prime_fortyFourAP_3496992739049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 614861506554349437030163) ^ 307430753277174718515081 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 614861506554349437030163) ^ 204953835518116479010054 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 614861506554349437030163) ^ 20981956434294 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 614861506554349437030163) ^ 175825788738 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_621509730110564998034623 : Nat.Prime 621509730110564998034623 := by
  apply lucas_primality 621509730110564998034623 (5 : ZMod 621509730110564998034623)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod) = 621509730110564998034623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_3061
      · exact prime_fortyFourAP_61379
      · exact prime_fortyFourAP_382747
      · exact prime_fortyFourAP_1440461809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 621509730110564998034623) ^ 310754865055282499017311 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 207169910036854999344874 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 203041401538897418502 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 10125771519747226218 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 1623813459310105626 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 431465607923358 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1274150510704293231697159 : Nat.Prime 1274150510704293231697159 := by
  apply lucas_primality 1274150510704293231697159 (3 : ZMod 1274150510704293231697159)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (212358418450715538616193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (212358418450715538616193, 1)] : List FactorBlock).map factorBlockValue).prod) = 1274150510704293231697159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_212358418450715538616193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1274150510704293231697159) ^ 637075255352146615848579 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1274150510704293231697159) ^ 424716836901431077232386 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1274150510704293231697159) ^ 6 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2554495330019847759305633 : Nat.Prime 2554495330019847759305633 := by
  apply lucas_primality 2554495330019847759305633 (3 : ZMod 2554495330019847759305633)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (53, 2), (28418646871883318789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (53, 2), (28418646871883318789, 1)] : List FactorBlock).map factorBlockValue).prod) = 2554495330019847759305633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_53
      · exact prime_fortyFourAP_28418646871883318789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2554495330019847759305633) ^ 1277247665009923879652816 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554495330019847759305633) ^ 48198025094714108666144 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554495330019847759305633) ^ 89888 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_3229034320330489122936059 : Nat.Prime 3229034320330489122936059 := by
  apply lucas_primality 3229034320330489122936059 (2 : ZMod 3229034320330489122936059)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (358993, 1), (4497349976643679853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (358993, 1), (4497349976643679853, 1)] : List FactorBlock).map factorBlockValue).prod) = 3229034320330489122936059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_358993
      · exact prime_fortyFourAP_4497349976643679853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3229034320330489122936059) ^ 1614517160165244561468029 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3229034320330489122936059) ^ 8994699953287359706 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3229034320330489122936059) ^ 717986 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_3554717978715606107045231 : Nat.Prime 3554717978715606107045231 := by
  apply lucas_primality 3554717978715606107045231 (19 : ZMod 3554717978715606107045231)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (293, 1), (1213214327206691504111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (293, 1), (1213214327206691504111, 1)] : List FactorBlock).map factorBlockValue).prod) = 3554717978715606107045231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_293
      · exact prime_fortyFourAP_1213214327206691504111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 3554717978715606107045231) ^ 1777358989357803053522615 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 3554717978715606107045231) ^ 710943595743121221409046 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 3554717978715606107045231) ^ 12132143272066915041110 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 3554717978715606107045231) ^ 2930 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_3994758324414389477077247 : Nat.Prime 3994758324414389477077247 := by
  apply lucas_primality 3994758324414389477077247 (5 : ZMod 3994758324414389477077247)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (22442462496710053242007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (22442462496710053242007, 1)] : List FactorBlock).map factorBlockValue).prod) = 3994758324414389477077247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_89
      · exact prime_fortyFourAP_22442462496710053242007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3994758324414389477077247) ^ 1997379162207194738538623 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3994758324414389477077247) ^ 44884924993420106484014 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3994758324414389477077247) ^ 178 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_5698920124947872455138027 : Nat.Prime 5698920124947872455138027 := by
  apply lucas_primality 5698920124947872455138027 (2 : ZMod 5698920124947872455138027)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (89, 1), (1217, 1), (974357259695558663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (89, 1), (1217, 1), (974357259695558663, 1)] : List FactorBlock).map factorBlockValue).prod) = 5698920124947872455138027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_89
      · exact prime_fortyFourAP_1217
      · exact prime_fortyFourAP_974357259695558663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5698920124947872455138027) ^ 2849460062473936227569013 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698920124947872455138027) ^ 1899640041649290818379342 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698920124947872455138027) ^ 64032810392672724215034 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698920124947872455138027) ^ 4682760990096854934378 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698920124947872455138027) ^ 5848902 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_7203952762847829908669147 : Nat.Prime 7203952762847829908669147 := by
  apply lucas_primality 7203952762847829908669147 (2 : ZMod 7203952762847829908669147)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (87853082473754023276453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (87853082473754023276453, 1)] : List FactorBlock).map factorBlockValue).prod) = 7203952762847829908669147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_41
      · exact prime_fortyFourAP_87853082473754023276453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7203952762847829908669147) ^ 3601976381423914954334573 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7203952762847829908669147) ^ 175706164947508046552906 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7203952762847829908669147) ^ 82 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_8436546042900450822332129 : Nat.Prime 8436546042900450822332129 := by
  apply lucas_primality 8436546042900450822332129 (3 : ZMod 8436546042900450822332129)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (13, 1), (1843650796088385232153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (13, 1), (1843650796088385232153, 1)] : List FactorBlock).map factorBlockValue).prod) = 8436546042900450822332129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_1843650796088385232153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8436546042900450822332129) ^ 4218273021450225411166064 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8436546042900450822332129) ^ 766958731172768256575648 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8436546042900450822332129) ^ 648965080223111601717856 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8436546042900450822332129) ^ 4576 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_8442022541467734464540719 : Nat.Prime 8442022541467734464540719 := by
  apply lucas_primality 8442022541467734464540719 (3 : ZMod 8442022541467734464540719)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37889, 1), (37134887616756554077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37889, 1), (37134887616756554077, 1)] : List FactorBlock).map factorBlockValue).prod) = 8442022541467734464540719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_37889
      · exact prime_fortyFourAP_37134887616756554077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8442022541467734464540719) ^ 4221011270733867232270359 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8442022541467734464540719) ^ 2814007513822578154846906 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8442022541467734464540719) ^ 222809325700539324462 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8442022541467734464540719) ^ 227334 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_16873092085800901644664259 : Nat.Prime 16873092085800901644664259 := by
  apply lucas_primality 16873092085800901644664259 (2 : ZMod 16873092085800901644664259)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8436546042900450822332129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8436546042900450822332129, 1)] : List FactorBlock).map factorBlockValue).prod) = 16873092085800901644664259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_8436546042900450822332129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 16873092085800901644664259) ^ 8436546042900450822332129 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 16873092085800901644664259) ^ 2 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_71357672017179944815500563 : Nat.Prime 71357672017179944815500563 := by
  apply lucas_primality 71357672017179944815500563 (2 : ZMod 71357672017179944815500563)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (466873793, 1), (5878517680718509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (466873793, 1), (5878517680718509, 1)] : List FactorBlock).map factorBlockValue).prod) = 71357672017179944815500563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_466873793
      · exact prime_fortyFourAP_5878517680718509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 71357672017179944815500563) ^ 35678836008589972407750281 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 71357672017179944815500563) ^ 5489051693629226524269274 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 71357672017179944815500563) ^ 152841459698681234 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (2 : ZMod 71357672017179944815500563) ^ 12138718618 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_525451948490143230005049601 : Nat.Prime 525451948490143230005049601 := by
  apply lucas_primality 525451948490143230005049601 (179 : ZMod 525451948490143230005049601)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 525451948490143230005049601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_23
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_31
      · exact prime_fortyFourAP_37
      · exact prime_fortyFourAP_41
      · exact prime_fortyFourAP_43
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_53
      · exact prime_fortyFourAP_59
      · exact prime_fortyFourAP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (179 : ZMod 525451948490143230005049601) ^ 262725974245071615002524800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 175150649496714410001683200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 105090389698028646001009920 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 75064564070020461429292800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 47768358953649384545913600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 40419380653087940769619200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 30908938146479013529708800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 27655365710007538421318400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 22845736890875792608915200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 18119032706556663103622400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 16950062854520749355001600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 14201404013247114324460800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12815901182686420244025600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12219812755584726279187200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 11179828691279643191596800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 9914187707361193018963200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8905965228646495423814400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8613966368690872623033600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_530813703066573262964284801 : Nat.Prime 530813703066573262964284801 := by
  apply lucas_primality 530813703066573262964284801 (103 : ZMod 530813703066573262964284801)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 530813703066573262964284801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_23
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_31
      · exact prime_fortyFourAP_37
      · exact prime_fortyFourAP_41
      · exact prime_fortyFourAP_43
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_53
      · exact prime_fortyFourAP_59
      · exact prime_fortyFourAP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 530813703066573262964284801) ^ 265406851533286631482142400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 176937901022191087654761600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 106162740613314652592856960 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 48255791187870296633116800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 40831823312813327920329600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 31224335474504309586134400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 27937563319293329629699200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 23078856655068402737577600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 18303920795399078033251200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 17123022679566879450460800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 14346316299096574674710400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 12946675684550567389372800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 12344504722478447975913600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 11293908575884537509878400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 10015352888048552131401600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 8996842424857173948547200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 8701863984697922343676800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_693596572006989063606665473 : Nat.Prime 693596572006989063606665473 := by
  apply lucas_primality 693596572006989063606665473 (60 : ZMod 693596572006989063606665473)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 693596572006989063606665473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_23
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_31
      · exact prime_fortyFourAP_37
      · exact prime_fortyFourAP_41
      · exact prime_fortyFourAP_43
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_53
      · exact prime_fortyFourAP_59
      · exact prime_fortyFourAP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (60 : ZMod 693596572006989063606665473) ^ 346798286003494531803332736 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (60 : ZMod 693596572006989063606665473) ^ 231198857335663021202221824 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (60 : ZMod 693596572006989063606665473) ^ 99085224572427009086666496 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (60 : ZMod 693596572006989063606665473) ^ 63054233818817187600605952 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (60 : ZMod 693596572006989063606665473) ^ 53353582462076081815897344 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (60 : ZMod 693596572006989063606665473) ^ 40799798353352297859215616 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (60 : ZMod 693596572006989063606665473) ^ 36505082737209950716140288 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (60 : ZMod 693596572006989063606665473) ^ 30156372695956046243768064 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (60 : ZMod 693596572006989063606665473) ^ 23917123172654795296781568 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (60 : ZMod 693596572006989063606665473) ^ 22374082967967389148602112 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (60 : ZMod 693596572006989063606665473) ^ 18745853297486190908288256 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (60 : ZMod 693596572006989063606665473) ^ 16916989561146074722113792 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (60 : ZMod 693596572006989063606665473) ^ 16130152837371838688527104 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (60 : ZMod 693596572006989063606665473) ^ 14757373872489129012907776 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (60 : ZMod 693596572006989063606665473) ^ 13086727773716774785031424 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (60 : ZMod 693596572006989063606665473) ^ 11755874101813373959435008 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (60 : ZMod 693596572006989063606665473) ^ 11370435606671951862404352 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_881690557636003046957625601 : Nat.Prime 881690557636003046957625601 := by
  apply lucas_primality 881690557636003046957625601 (89 : ZMod 881690557636003046957625601)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 881690557636003046957625601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_23
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_31
      · exact prime_fortyFourAP_37
      · exact prime_fortyFourAP_41
      · exact prime_fortyFourAP_43
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_53
      · exact prime_fortyFourAP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (89 : ZMod 881690557636003046957625601) ^ 440845278818001523478812800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (89 : ZMod 881690557636003046957625601) ^ 293896852545334348985875200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (89 : ZMod 881690557636003046957625601) ^ 176338111527200609391525120 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (89 : ZMod 881690557636003046957625601) ^ 125955793948000435279660800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (89 : ZMod 881690557636003046957625601) ^ 80153687057818458814329600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (89 : ZMod 881690557636003046957625601) ^ 67822350587384849765971200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (89 : ZMod 881690557636003046957625601) ^ 51864150449176649821036800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (89 : ZMod 881690557636003046957625601) ^ 46404766191368581418822400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (89 : ZMod 881690557636003046957625601) ^ 38334372071130567259027200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (89 : ZMod 881690557636003046957625601) ^ 30403122677103553343366400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (89 : ZMod 881690557636003046957625601) ^ 28441630891483969256697600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (89 : ZMod 881690557636003046957625601) ^ 23829474530702785052908800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (89 : ZMod 881690557636003046957625601) ^ 21504647747219586511161600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (89 : ZMod 881690557636003046957625601) ^ 20504431572930303417619200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (89 : ZMod 881690557636003046957625601) ^ 18759373566723469084204800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (89 : ZMod 881690557636003046957625601) ^ 16635670898792510319955200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (89 : ZMod 881690557636003046957625601) ^ 14453943567803328638649600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_912627068430248767903507201 : Nat.Prime 912627068430248767903507201 := by
  apply lucas_primality 912627068430248767903507201 (67 : ZMod 912627068430248767903507201)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 912627068430248767903507201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_23
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_31
      · exact prime_fortyFourAP_37
      · exact prime_fortyFourAP_41
      · exact prime_fortyFourAP_43
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_53
      · exact prime_fortyFourAP_59
      · exact prime_fortyFourAP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 912627068430248767903507201) ^ 456313534215124383951753600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (67 : ZMod 912627068430248767903507201) ^ 304209022810082922634502400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (67 : ZMod 912627068430248767903507201) ^ 182525413686049753580701440 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (67 : ZMod 912627068430248767903507201) ^ 130375295490035538271929600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (67 : ZMod 912627068430248767903507201) ^ 82966097130022615263955200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (67 : ZMod 912627068430248767903507201) ^ 70202082186942212915654400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (67 : ZMod 912627068430248767903507201) ^ 53683945201779339288441600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (67 : ZMod 912627068430248767903507201) ^ 39679437757836902952326400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (67 : ZMod 912627068430248767903507201) ^ 31469898911387888548396800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (67 : ZMod 912627068430248767903507201) ^ 29439582852588669932371200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (67 : ZMod 912627068430248767903507201) ^ 24665596444060777510905600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (67 : ZMod 912627068430248767903507201) ^ 22259196790981677265939200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (67 : ZMod 912627068430248767903507201) ^ 21223885312331366695430400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (67 : ZMod 912627068430248767903507201) ^ 19417597200643590806457600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (67 : ZMod 912627068430248767903507201) ^ 17219378649627335243462400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (67 : ZMod 912627068430248767903507201) ^ 15468255397122860472940800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (67 : ZMod 912627068430248767903507201) ^ 14961099482463094555795200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_1576355845470429690015148801 : Nat.Prime 1576355845470429690015148801 := by
  apply lucas_primality 1576355845470429690015148801 (101 : ZMod 1576355845470429690015148801)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1576355845470429690015148801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_23
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_31
      · exact prime_fortyFourAP_37
      · exact prime_fortyFourAP_41
      · exact prime_fortyFourAP_43
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_53
      · exact prime_fortyFourAP_59
      · exact prime_fortyFourAP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 1576355845470429690015148801) ^ 788177922735214845007574400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 525451948490143230005049600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 315271169094085938003029760 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 225193692210061384287878400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 143305076860948153637740800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 121258141959263822308857600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 92726814439437040589126400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 82966097130022615263955200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 68537210672627377826745600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 54357098119669989310867200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 50850188563562248065004800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 42604212039741342973382400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 38447703548059260732076800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 36659438266754178837561600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 33539486073838929574790400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 29742563122083579056889600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 26717895685939486271443200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 25841899106072617869100800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_2737881205290746303710521601 : Nat.Prime 2737881205290746303710521601 := by
  apply lucas_primality 2737881205290746303710521601 (19 : ZMod 2737881205290746303710521601)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2737881205290746303710521601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_23
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_31
      · exact prime_fortyFourAP_37
      · exact prime_fortyFourAP_41
      · exact prime_fortyFourAP_43
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_53
      · exact prime_fortyFourAP_59
      · exact prime_fortyFourAP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 2737881205290746303710521601) ^ 1368940602645373151855260800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2737881205290746303710521601) ^ 912627068430248767903507200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2737881205290746303710521601) ^ 547576241058149260742104320 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2737881205290746303710521601) ^ 391125886470106614815788800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2737881205290746303710521601) ^ 248898291390067845791865600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2737881205290746303710521601) ^ 210606246560826638746963200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2737881205290746303710521601) ^ 161051835605338017865324800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2737881205290746303710521601) ^ 119038313273510708856979200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2737881205290746303710521601) ^ 94409696734163665645190400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2737881205290746303710521601) ^ 88318748557766009797113600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2737881205290746303710521601) ^ 73996789332182332532716800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2737881205290746303710521601) ^ 66777590372945031797817600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2737881205290746303710521601) ^ 63671655936994100086291200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2737881205290746303710521601) ^ 58252791601930772419372800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2737881205290746303710521601) ^ 51658135948882005730387200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2737881205290746303710521601) ^ 46404766191368581418822400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (19 : ZMod 2737881205290746303710521601) ^ 44883298447389283667385600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_7431391842932025681499987201 : Nat.Prime 7431391842932025681499987201 := by
  apply lucas_primality 7431391842932025681499987201 (71 : ZMod 7431391842932025681499987201)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 2), (7, 1), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 2), (7, 1), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 7431391842932025681499987201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_23
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_31
      · exact prime_fortyFourAP_37
      · exact prime_fortyFourAP_41
      · exact prime_fortyFourAP_43
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_53
      · exact prime_fortyFourAP_59
      · exact prime_fortyFourAP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 7431391842932025681499987201) ^ 3715695921466012840749993600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 7431391842932025681499987201) ^ 2477130614310675227166662400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 7431391842932025681499987201) ^ 1486278368586405136299997440 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 7431391842932025681499987201) ^ 1061627406133146525928569600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 7431391842932025681499987201) ^ 675581076630184152863635200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 7431391842932025681499987201) ^ 571645526379386590884614400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 7431391842932025681499987201) ^ 437140696643060334205881600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 7431391842932025681499987201) ^ 391125886470106614815788800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 7431391842932025681499987201) ^ 323103993170957638326086400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 7431391842932025681499987201) ^ 256254891135587092465516800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 7431391842932025681499987201) ^ 239722317513936312306451200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 7431391842932025681499987201) ^ 200848428187352045445945600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 7431391842932025681499987201) ^ 181253459583707943451219200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 7431391842932025681499987201) ^ 172823066114698271662790400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 7431391842932025681499987201) ^ 158114720062383525138297600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 7431391842932025681499987201) ^ 140214940432679729839622400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 7431391842932025681499987201) ^ 125955793948000435279660800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 7431391842932025681499987201) ^ 121826095785770912811475200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_10403948580104835954099982081 : Nat.Prime 10403948580104835954099982081 := by
  apply lucas_primality 10403948580104835954099982081 (109 : ZMod 10403948580104835954099982081)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 1), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 1), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 10403948580104835954099982081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_23
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_31
      · exact prime_fortyFourAP_37
      · exact prime_fortyFourAP_41
      · exact prime_fortyFourAP_43
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_53
      · exact prime_fortyFourAP_59
      · exact prime_fortyFourAP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (109 : ZMod 10403948580104835954099982081) ^ 5201974290052417977049991040 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (109 : ZMod 10403948580104835954099982081) ^ 3467982860034945318033327360 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (109 : ZMod 10403948580104835954099982081) ^ 2080789716020967190819996416 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (109 : ZMod 10403948580104835954099982081) ^ 1486278368586405136299997440 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (109 : ZMod 10403948580104835954099982081) ^ 945813507282257814009089280 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (109 : ZMod 10403948580104835954099982081) ^ 800303736931141227238460160 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (109 : ZMod 10403948580104835954099982081) ^ 611996975300284467888234240 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (109 : ZMod 10403948580104835954099982081) ^ 547576241058149260742104320 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (109 : ZMod 10403948580104835954099982081) ^ 452345590439340693656520960 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (109 : ZMod 10403948580104835954099982081) ^ 358756847589821929451723520 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (109 : ZMod 10403948580104835954099982081) ^ 335611244519510837229031680 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (109 : ZMod 10403948580104835954099982081) ^ 281187799462292863624323840 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (109 : ZMod 10403948580104835954099982081) ^ 253754843417191120831706880 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (109 : ZMod 10403948580104835954099982081) ^ 241952292560577580327906560 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (109 : ZMod 10403948580104835954099982081) ^ 221360608087336935193616640 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (109 : ZMod 10403948580104835954099982081) ^ 196300916605751621775471360 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (109 : ZMod 10403948580104835954099982081) ^ 176338111527200609391525120 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (109 : ZMod 10403948580104835954099982081) ^ 170556534100079277936065280 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_17339914300174726590166636801 : Nat.Prime 17339914300174726590166636801 := by
  apply lucas_primality 17339914300174726590166636801 (71 : ZMod 17339914300174726590166636801)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 17339914300174726590166636801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_3
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_11
      · exact prime_fortyFourAP_13
      · exact prime_fortyFourAP_17
      · exact prime_fortyFourAP_19
      · exact prime_fortyFourAP_23
      · exact prime_fortyFourAP_29
      · exact prime_fortyFourAP_31
      · exact prime_fortyFourAP_37
      · exact prime_fortyFourAP_41
      · exact prime_fortyFourAP_43
      · exact prime_fortyFourAP_47
      · exact prime_fortyFourAP_53
      · exact prime_fortyFourAP_59
      · exact prime_fortyFourAP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 17339914300174726590166636801) ^ 8669957150087363295083318400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 17339914300174726590166636801) ^ 5779971433391575530055545600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 17339914300174726590166636801) ^ 3467982860034945318033327360 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 17339914300174726590166636801) ^ 2477130614310675227166662400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 17339914300174726590166636801) ^ 1576355845470429690015148800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 17339914300174726590166636801) ^ 1333839561551902045397433600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 17339914300174726590166636801) ^ 1019994958833807446480390400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 17339914300174726590166636801) ^ 912627068430248767903507200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 17339914300174726590166636801) ^ 753909317398901156094201600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 17339914300174726590166636801) ^ 597928079316369882419539200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 17339914300174726590166636801) ^ 559352074199184728715052800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 17339914300174726590166636801) ^ 468646332437154772707206400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 17339914300174726590166636801) ^ 422924739028651868052844800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 17339914300174726590166636801) ^ 403253820934295967213177600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 17339914300174726590166636801) ^ 368934346812228225322694400 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 17339914300174726590166636801) ^ 327168194342919369625785600 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 17339914300174726590166636801) ^ 293896852545334348985875200 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (71 : ZMod 17339914300174726590166636801) ^ 284260890166798796560108800 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem prime_fortyFourAP_52019742900524179770499910471 : Nat.Prime 52019742900524179770499910471 := by
  apply lucas_primality 52019742900524179770499910471 (13 : ZMod 52019742900524179770499910471)
  · rw [← fortyFourAPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (293, 1), (8971, 1), (282723354051033066407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (293, 1), (8971, 1), (282723354051033066407, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFourAP_2
      · exact prime_fortyFourAP_5
      · exact prime_fortyFourAP_7
      · exact prime_fortyFourAP_293
      · exact prime_fortyFourAP_8971
      · exact prime_fortyFourAP_282723354051033066407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 52019742900524179770499910471) ^ 26009871450262089885249955235 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 52019742900524179770499910471) ^ 10403948580104835954099982094 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 52019742900524179770499910471) ^ 7431391842932025681499987210 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 52019742900524179770499910471) ^ 177541784643427234711603790 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 52019742900524179770499910471) ^ 5798655991586688192007570 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide
    · change (13 : ZMod 52019742900524179770499910471) ^ 183995210 ≠ 1
      rw [← fortyFourAPFastPow_eq_pow]
      decide

private theorem phi_fortyFourAP_52019742900524179770499910400 : Nat.totient 52019742900524179770499910400 = 6845140212211868132966400000 := by
  rw [← show ((([(2, 8), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910400 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_3, prime_fortyFourAP_5, prime_fortyFourAP_7, prime_fortyFourAP_11, prime_fortyFourAP_13, prime_fortyFourAP_17, prime_fortyFourAP_19, prime_fortyFourAP_23, prime_fortyFourAP_29, prime_fortyFourAP_31, prime_fortyFourAP_37, prime_fortyFourAP_41, prime_fortyFourAP_43, prime_fortyFourAP_47, prime_fortyFourAP_53, prime_fortyFourAP_59, prime_fortyFourAP_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910401 : Nat.totient 52019742900524179770499910401 = 52019742899557984920820844292 := by
  rw [← show ((([(53839808623, 1), (966194795839257487, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_53839808623, prime_fortyFourAP_966194795839257487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910402 : Nat.totient 52019742900524179770499910402 = 26009424537446711085114733728 := by
  rw [← show ((([(2, 1), (58199, 1), (224916175177, 1), (1987018880687, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_58199, prime_fortyFourAP_224916175177, prime_fortyFourAP_1987018880687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910403 : Nat.totient 52019742900524179770499910403 = 34679828600349453180333273600 := by
  rw [← show ((([(3, 1), (17339914300174726590166636801, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3, prime_fortyFourAP_17339914300174726590166636801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910404 : Nat.totient 52019742900524179770499910404 = 25696470798114530233657925120 := by
  rw [← show ((([(2, 2), (83, 1), (895529, 1), (2064319931, 1), (84756586553, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_83, prime_fortyFourAP_895529, prime_fortyFourAP_2064319931, prime_fortyFourAP_84756586553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910405 : Nat.totient 52019742900524179770499910405 = 41615794320419343816399928320 := by
  rw [← show ((([(5, 1), (10403948580104835954099982081, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_5, prime_fortyFourAP_10403948580104835954099982081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910406 : Nat.totient 52019742900524179770499910406 = 17145083756042899792873461504 := by
  rw [← show ((([(2, 1), (3, 1), (89, 1), (369688933, 1), (263505991609941173, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_3, prime_fortyFourAP_89, prime_fortyFourAP_369688933, prime_fortyFourAP_263505991609941173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910407 : Nat.totient 52019742900524179770499910407 = 44588351057592154088999923200 := by
  rw [← show ((([(7, 1), (7431391842932025681499987201, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_7, prime_fortyFourAP_7431391842932025681499987201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910408 : Nat.totient 52019742900524179770499910408 = 26009869129425253958775645888 := by
  rw [← show ((([(2, 3), (11218483, 1), (15837208853, 1), (36598681199, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_11218483, prime_fortyFourAP_15837208853, prime_fortyFourAP_36598681199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910409 : Nat.totient 52019742900524179770499910409 = 34679828461067915479490475000 := by
  rw [← show ((([(3, 2), (248990851, 1), (23213589616558142251, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3, prime_fortyFourAP_248990851, prime_fortyFourAP_23213589616558142251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910410 : Nat.totient 52019742900524179770499910410 = 20807585435853839134535784000 := by
  rw [← show ((([(2, 1), (5, 1), (66751, 1), (103039496123, 1), (756321939917, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_5, prime_fortyFourAP_66751, prime_fortyFourAP_103039496123, prime_fortyFourAP_756321939917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910411 : Nat.totient 52019742900524179770499910411 = 47167596329455081740579840000 := by
  rw [← show ((([(11, 1), (401, 1), (11069, 1), (53269, 1), (20000838920189041, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_11, prime_fortyFourAP_401, prime_fortyFourAP_11069, prime_fortyFourAP_53269, prime_fortyFourAP_20000838920189041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910412 : Nat.totient 52019742900524179770499910412 = 17329696318854647199129407488 := by
  rw [← show ((([(2, 2), (3, 1), (1697, 1), (2554495330019847759305633, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_3, prime_fortyFourAP_1697, prime_fortyFourAP_2554495330019847759305633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910413 : Nat.totient 52019742900524179770499910413 = 48018224215859303713588951104 := by
  rw [← show ((([(13, 1), (5272876883773, 1), (758887183004437, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_13, prime_fortyFourAP_5272876883773, prime_fortyFourAP_758887183004437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910414 : Nat.totient 52019742900524179770499910414 = 22293512605661595667472638080 := by
  rw [← show ((([(2, 1), (7, 1), (67121, 1), (67399, 1), (821350062669399719, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_7, prime_fortyFourAP_67121, prime_fortyFourAP_67399, prime_fortyFourAP_821350062669399719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910415 : Nat.totient 52019742900524179770499910415 = 27722516461644185258042448000 := by
  rw [← show ((([(3, 1), (5, 1), (1663, 1), (9431, 1), (16087, 1), (13745226048974351, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3, prime_fortyFourAP_5, prime_fortyFourAP_1663, prime_fortyFourAP_9431, prime_fortyFourAP_16087, prime_fortyFourAP_13745226048974351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910416 : Nat.totient 52019742900524179770499910416 = 26003694454464941181141429120 := by
  rw [← show ((([(2, 4), (4211, 1), (75111599, 1), (10279120799235109, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_4211, prime_fortyFourAP_75111599, prime_fortyFourAP_10279120799235109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910417 : Nat.totient 52019742900524179770499910417 = 48954110321457803233635316992 := by
  rw [← show ((([(17, 1), (8669, 1), (2418018503, 1), (145979091766243, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_17, prime_fortyFourAP_8669, prime_fortyFourAP_2418018503, prime_fortyFourAP_145979091766243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910418 : Nat.totient 52019742900524179770499910418 = 17215166677116362258150379648 := by
  rw [← show ((([(2, 1), (3, 2), (139, 1), (451071857, 1), (46093020050440787, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_3, prime_fortyFourAP_139, prime_fortyFourAP_451071857, prime_fortyFourAP_46093020050440787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910419 : Nat.totient 52019742900524179770499910419 = 49281861695233433466789388800 := by
  rw [← show ((([(19, 1), (2737881205290746303710521601, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_19, prime_fortyFourAP_2737881205290746303710521601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910420 : Nat.totient 52019742900524179770499910420 = 20757324115310651790749452800 := by
  rw [← show ((([(2, 2), (5, 1), (631, 1), (1181, 1), (3446959, 1), (1012564812501629, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_5, prime_fortyFourAP_631, prime_fortyFourAP_1181, prime_fortyFourAP_3446959, prime_fortyFourAP_1012564812501629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910421 : Nat.totient 52019742900524179770499910421 = 29687632274443875404758396416 := by
  rw [← show ((([(3, 1), (7, 1), (809, 1), (24919, 1), (328801117, 1), (373711524443, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3, prime_fortyFourAP_7, prime_fortyFourAP_809, prime_fortyFourAP_24919, prime_fortyFourAP_328801117, prime_fortyFourAP_373711524443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910422 : Nat.totient 52019742900524179770499910422 = 23645225188597186210076075520 := by
  rw [← show ((([(2, 1), (11, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_11, prime_fortyFourAP_210193, prime_fortyFourAP_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910423 : Nat.totient 52019742900524179770499910423 = 49757889492877918092752396088 := by
  rw [← show ((([(23, 1), (396619, 1), (5702520434464066190179, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_23, prime_fortyFourAP_396619, prime_fortyFourAP_5702520434464066190179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910424 : Nat.totient 52019742900524179770499910424 = 17339914297179711992819367936 := by
  rw [← show ((([(2, 3), (3, 1), (5789592673, 1), (374376818878815937, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_3, prime_fortyFourAP_5789592673, prime_fortyFourAP_374376818878815937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910425 : Nat.totient 52019742900524179770499910425 = 41612572262470098244246214400 := by
  rw [← show ((([(5, 2), (12919, 1), (53908471, 1), (2987736414979633, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_5, prime_fortyFourAP_12919, prime_fortyFourAP_53908471, prime_fortyFourAP_2987736414979633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910426 : Nat.totient 52019742900524179770499910426 = 24009112097395452476355364848 := by
  rw [← show ((([(2, 1), (13, 1), (2278167139, 1), (878232026121702859, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_13, prime_fortyFourAP_2278167139, prime_fortyFourAP_878232026121702859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910427 : Nat.totient 52019742900524179770499910427 = 34679828600349453180333273132 := by
  rw [← show ((([(3, 6), (71357672017179944815500563, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3, prime_fortyFourAP_71357672017179944815500563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910428 : Nat.totient 52019742900524179770499910428 = 22293490207855165419371401200 := by
  rw [← show ((([(2, 2), (7, 1), (32531, 1), (57110078409302094014171, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_7, prime_fortyFourAP_32531, prime_fortyFourAP_57110078409302094014171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910429 : Nat.totient 52019742900524179770499910429 = 50082400501981453534108897920 := by
  rw [← show ((([(29, 1), (359, 1), (13711, 1), (364423709151875422649, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_29, prime_fortyFourAP_359, prime_fortyFourAP_13711, prime_fortyFourAP_364423709151875422649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910430 : Nat.totient 52019742900524179770499910430 = 13854778830242677488074332160 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (977, 1), (4691, 1), (6385035269, 1), (59254815407, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_3, prime_fortyFourAP_5, prime_fortyFourAP_977, prime_fortyFourAP_4691, prime_fortyFourAP_6385035269, prime_fortyFourAP_59254815407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910431 : Nat.totient 52019742900524179770499910431 = 50341686677906683368800691360 := by
  rw [← show ((([(31, 1), (2534037753277, 1), (662206480715413, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_31, prime_fortyFourAP_2534037753277, prime_fortyFourAP_662206480715413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910432 : Nat.totient 52019742900524179770499910432 = 25978731146058131226759333888 := by
  rw [← show ((([(2, 5), (857, 1), (32869, 1), (57709978139285874797, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_857, prime_fortyFourAP_32869, prime_fortyFourAP_57709978139285874797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910433 : Nat.totient 52019742900524179770499910433 = 31527116909408593800302976000 := by
  rw [← show ((([(3, 1), (11, 1), (1576355845470429690015148801, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3, prime_fortyFourAP_11, prime_fortyFourAP_1576355845470429690015148801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910434 : Nat.totient 52019742900524179770499910434 = 24415962878820748483896127552 := by
  rw [← show ((([(2, 1), (17, 1), (383, 1), (3994758324414389477077247, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_17, prime_fortyFourAP_383, prime_fortyFourAP_3994758324414389477077247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910435 : Nat.totient 52019742900524179770499910435 = 35670680842008846757822869600 := by
  rw [← show ((([(5, 1), (7, 1), (8775342271, 1), (169369845948702271, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_5, prime_fortyFourAP_7, prime_fortyFourAP_8775342271, prime_fortyFourAP_169369845948702271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910436 : Nat.totient 52019742900524179770499910436 = 17168231315556908757322444800 := by
  rw [← show ((([(2, 2), (3, 2), (101, 1), (25824109, 1), (554011756364663489, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_3, prime_fortyFourAP_101, prime_fortyFourAP_25824109, prime_fortyFourAP_554011756364663489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910437 : Nat.totient 52019742900524179770499910437 = 50613802944811249935584407680 := by
  rw [← show ((([(37, 1), (60338441, 1), (426605947, 1), (54619219163, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_37, prime_fortyFourAP_60338441, prime_fortyFourAP_426605947, prime_fortyFourAP_54619219163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910438 : Nat.totient 52019742900524179770499910438 = 24279540703258704522081246720 := by
  rw [← show ((([(2, 1), (19, 1), (131, 1), (173, 1), (1103, 1), (4339, 1), (5639, 1), (2238205449829, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_19, prime_fortyFourAP_131, prime_fortyFourAP_173, prime_fortyFourAP_1103, prime_fortyFourAP_4339, prime_fortyFourAP_5639, prime_fortyFourAP_2238205449829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910439 : Nat.totient 52019742900524179770499910439 = 31728854533799771825024636928 := by
  rw [← show ((([(3, 1), (13, 1), (113, 1), (20015173, 1), (589747084636144349, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3, prime_fortyFourAP_13, prime_fortyFourAP_113, prime_fortyFourAP_20015173, prime_fortyFourAP_589747084636144349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910440 : Nat.totient 52019742900524179770499910440 = 20514256486030314162882693120 := by
  rw [← show ((([(2, 3), (5, 1), (71, 1), (37967, 1), (834527, 1), (3072847, 1), (188131817, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_5, prime_fortyFourAP_71, prime_fortyFourAP_37967, prime_fortyFourAP_834527, prime_fortyFourAP_3072847, prime_fortyFourAP_188131817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910441 : Nat.totient 52019742900524179770499910441 = 50055695824764020789554790400 := by
  rw [← show ((([(41, 1), (73, 1), (925081, 1), (18788050697403655777, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_41, prime_fortyFourAP_73, prime_fortyFourAP_925081, prime_fortyFourAP_18788050697403655777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910442 : Nat.totient 52019742900524179770499910442 = 14856036099828633646526056896 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (2203, 1), (28231919, 1), (35140247, 1), (566707819, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_3, prime_fortyFourAP_7, prime_fortyFourAP_2203, prime_fortyFourAP_28231919, prime_fortyFourAP_35140247, prime_fortyFourAP_566707819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910443 : Nat.totient 52019742900524179770499910443 = 50760108162297608388260034816 := by
  rw [← show ((([(43, 1), (1019, 1), (5049487, 1), (82829689, 1), (2838522053, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_43, prime_fortyFourAP_1019, prime_fortyFourAP_5049487, prime_fortyFourAP_82829689, prime_fortyFourAP_2838522053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910444 : Nat.totient 52019742900524179770499910444 = 23411096557065912790019523840 := by
  rw [← show ((([(2, 2), (11, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_11, prime_fortyFourAP_103, prime_fortyFourAP_5009, prime_fortyFourAP_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910445 : Nat.totient 52019742900524179770499910445 = 27681231306216415619045128320 := by
  rw [← show ((([(3, 2), (5, 1), (443, 1), (6372167, 1), (409510283668397941, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3, prime_fortyFourAP_5, prime_fortyFourAP_443, prime_fortyFourAP_6372167, prime_fortyFourAP_409510283668397941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910446 : Nat.totient 52019742900524179770499910446 = 24856004456030461516996496160 := by
  rw [← show ((([(2, 1), (23, 1), (1327, 1), (5843, 1), (145849035197483064341, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_23, prime_fortyFourAP_1327, prime_fortyFourAP_5843, prime_fortyFourAP_145849035197483064341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910447 : Nat.totient 52019742900524179770499910447 = 50912935979059571897384717280 := by
  rw [← show ((([(47, 1), (13190663, 1), (2586028147, 1), (32446695341, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_47, prime_fortyFourAP_13190663, prime_fortyFourAP_2586028147, prime_fortyFourAP_32446695341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910448 : Nat.totient 52019742900524179770499910448 = 17258724639537494549464301568 := by
  rw [← show ((([(2, 4), (3, 1), (257, 1), (1259, 1), (3349408442130034682227, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_3, prime_fortyFourAP_257, prime_fortyFourAP_1259, prime_fortyFourAP_3349408442130034682227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910449 : Nat.totient 52019742900524179770499910449 = 44060384747791315723879600128 := by
  rw [← show ((([(7, 3), (97, 1), (787, 1), (3607, 1), (22748147, 1), (24212266553, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_7, prime_fortyFourAP_97, prime_fortyFourAP_787, prime_fortyFourAP_3607, prime_fortyFourAP_22748147, prime_fortyFourAP_24212266553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910450 : Nat.totient 52019742900524179770499910450 = 20741403834572171111382528000 := by
  rw [← show ((([(2, 1), (5, 2), (313, 1), (2029241, 1), (4938853, 1), (331660790141, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_5, prime_fortyFourAP_313, prime_fortyFourAP_2029241, prime_fortyFourAP_4938853, prime_fortyFourAP_331660790141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910451 : Nat.totient 52019742900524179770499910451 = 32638168351174741185892638720 := by
  rw [← show ((([(3, 1), (17, 1), (19541, 1), (5839099949, 1), (8939337443089, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3, prime_fortyFourAP_17, prime_fortyFourAP_19541, prime_fortyFourAP_5839099949, prime_fortyFourAP_8939337443089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910452 : Nat.totient 52019742900524179770499910452 = 23994355431776932430665041888 := by
  rw [← show ((([(2, 2), (13, 1), (1627, 1), (614861506554349437030163, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_13, prime_fortyFourAP_1627, prime_fortyFourAP_614861506554349437030163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910453 : Nat.totient 52019742900524179770499910453 = 50960790307558623547986752640 := by
  rw [← show ((([(53, 1), (659, 1), (147601178531, 1), (10090602355369, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_53, prime_fortyFourAP_659, prime_fortyFourAP_147601178531, prime_fortyFourAP_10090602355369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910454 : Nat.totient 52019742900524179770499910454 = 17275929376557845680239817800 := by
  rw [← show ((([(2, 1), (3, 3), (271, 1), (3554717978715606107045231, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_3, prime_fortyFourAP_271, prime_fortyFourAP_3554717978715606107045231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910455 : Nat.totient 52019742900524179770499910455 = 37441966897856195695599040000 := by
  rw [← show ((([(5, 1), (11, 1), (107, 1), (1013, 1), (144417341, 1), (60421700572451, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_5, prime_fortyFourAP_11, prime_fortyFourAP_107, prime_fortyFourAP_1013, prime_fortyFourAP_144417341, prime_fortyFourAP_60421700572451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910456 : Nat.totient 52019742900524179770499910456 = 22157401445797328105576645088 := by
  rw [← show ((([(2, 3), (7, 1), (163, 1), (5698920124947872455138027, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_7, prime_fortyFourAP_163, prime_fortyFourAP_5698920124947872455138027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910457 : Nat.totient 52019742900524179770499910457 = 32854574463488955644526259200 := by
  rw [← show ((([(3, 1), (19, 1), (912627068430248767903507201, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3, prime_fortyFourAP_19, prime_fortyFourAP_912627068430248767903507201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910458 : Nat.totient 52019742900524179770499910458 = 24929672912791419929195351424 := by
  rw [← show ((([(2, 1), (29, 1), (137, 1), (2340867574039, 1), (2796680117807, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_29, prime_fortyFourAP_137, prime_fortyFourAP_2340867574039, prime_fortyFourAP_2796680117807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910459 : Nat.totient 52019742900524179770499910459 = 51138052342888176723542284800 := by
  rw [← show ((([(59, 1), (881690557636003046957625601, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_59, prime_fortyFourAP_881690557636003046957625601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910460 : Nat.totient 52019742900524179770499910460 = 13868321321242346890427854848 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (4493, 1), (31159, 1), (222419, 1), (940573, 1), (29602789, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_3, prime_fortyFourAP_5, prime_fortyFourAP_4493, prime_fortyFourAP_31159, prime_fortyFourAP_222419, prime_fortyFourAP_940573, prime_fortyFourAP_29602789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910461 : Nat.totient 52019742900524179770499910461 = 51166946696658249444837304320 := by
  rw [← show ((([(61, 1), (6785893, 1), (8537549, 1), (14719672578593, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_61, prime_fortyFourAP_6785893, prime_fortyFourAP_8537549, prime_fortyFourAP_14719672578593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910462 : Nat.totient 52019742900524179770499910462 = 24915617903694343493422540800 := by
  rw [← show ((([(2, 1), (31, 1), (109, 1), (1033, 1), (159671, 1), (24507097, 1), (1904284259, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910462 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_31, prime_fortyFourAP_109, prime_fortyFourAP_1033, prime_fortyFourAP_159671, prime_fortyFourAP_24507097, prime_fortyFourAP_1904284259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910463 : Nat.totient 52019742900524179770499910463 = 29725567336373569425759160512 := by
  rw [← show ((([(3, 2), (7, 1), (840785173, 1), (982070368610347837, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910463 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3, prime_fortyFourAP_7, prime_fortyFourAP_840785173, prime_fortyFourAP_982070368610347837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910464 : Nat.totient 52019742900524179770499910464 = 25480108256709295607880337920 := by
  rw [← show ((([(2, 6), (67, 1), (181, 1), (67024695540586320517363, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910464 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_67, prime_fortyFourAP_181, prime_fortyFourAP_67024695540586320517363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910465 : Nat.totient 52019742900524179770499910465 = 38414579372687706466508829696 := by
  rw [← show ((([(5, 1), (13, 1), (5648096221913, 1), (141694423304297, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910465 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_5, prime_fortyFourAP_13, prime_fortyFourAP_5648096221913, prime_fortyFourAP_141694423304297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910466 : Nat.totient 52019742900524179770499910466 = 15715497292608989121442560000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910466 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_3, prime_fortyFourAP_11, prime_fortyFourAP_421, prime_fortyFourAP_1483, prime_fortyFourAP_2072201, prime_fortyFourAP_2567179, prime_fortyFourAP_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910467 : Nat.totient 52019742900524179770499910467 = 51951674477087469982826398080 := by
  rw [← show ((([(1039, 1), (2887, 1), (2062421371, 1), (8408692477489, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910467 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_1039, prime_fortyFourAP_2887, prime_fortyFourAP_2062421371, prime_fortyFourAP_8408692477489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910468 : Nat.totient 52019742900524179770499910468 = 24479878984497584795784328704 := by
  rw [← show ((([(2, 2), (17, 1), (889731133, 1), (859806059102301397, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910468 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_17, prime_fortyFourAP_889731133, prime_fortyFourAP_859806059102301397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910469 : Nat.totient 52019742900524179770499910469 = 33076951832498263297475788800 := by
  rw [← show ((([(3, 1), (23, 1), (349, 1), (4033241, 1), (27770209, 1), (19286808221, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910469 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3, prime_fortyFourAP_23, prime_fortyFourAP_349, prime_fortyFourAP_4033241, prime_fortyFourAP_27770209, prime_fortyFourAP_19286808221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910470 : Nat.totient 52019742900524179770499910470 = 17772487628751068372478034560 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (293, 1), (8971, 1), (282723354051033066407, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910470 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_5, prime_fortyFourAP_7, prime_fortyFourAP_293, prime_fortyFourAP_8971, prime_fortyFourAP_282723354051033066407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910471 : Nat.totient 52019742900524179770499910471 = 52019742900524179770499910470 := by
  rw [← show ((([(52019742900524179770499910471, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910471 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_52019742900524179770499910471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910472 : Nat.totient 52019742900524179770499910472 = 17339657083528612530139747200 := by
  rw [← show ((([(2, 3), (3, 2), (67901, 1), (9392503, 1), (1132865085569267, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910472 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_3, prime_fortyFourAP_67901, prime_fortyFourAP_9392503, prime_fortyFourAP_1132865085569267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910473 : Nat.totient 52019742900524179770499910473 = 52013108575380303676224184320 := by
  rw [← show ((([(7841, 1), (811224881569, 1), (8178157776137, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910473 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_7841, prime_fortyFourAP_811224881569, prime_fortyFourAP_8178157776137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910474 : Nat.totient 52019742900524179770499910474 = 25306861868512926857997926400 := by
  rw [← show ((([(2, 1), (37, 1), (631361, 1), (1113419261968560235841, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910474 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_37, prime_fortyFourAP_631361, prime_fortyFourAP_1113419261968560235841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910475 : Nat.totient 52019742900524179770499910475 = 27743862880279562544266618880 := by
  rw [← show ((([(3, 1), (5, 2), (693596572006989063606665473, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910475 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3, prime_fortyFourAP_5, prime_fortyFourAP_693596572006989063606665473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910476 : Nat.totient 52019742900524179770499910476 = 24500404439341586928156672000 := by
  rw [← show ((([(2, 2), (19, 1), (241, 1), (641, 1), (4430773372276762682321, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910476 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_19, prime_fortyFourAP_241, prime_fortyFourAP_641, prime_fortyFourAP_4430773372276762682321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910477 : Nat.totient 52019742900524179770499910477 = 40497574014004415271935969520 := by
  rw [← show ((([(7, 1), (11, 1), (1087, 1), (621509730110564998034623, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910477 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_7, prime_fortyFourAP_11, prime_fortyFourAP_1087, prime_fortyFourAP_621509730110564998034623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910478 : Nat.totient 52019742900524179770499910478 = 15803466197627598917620224096 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (79, 1), (8442022541467734464540719, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910478 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_3, prime_fortyFourAP_13, prime_fortyFourAP_79, prime_fortyFourAP_8442022541467734464540719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910479 : Nat.totient 52019742900524179770499910479 = 52019742900515272915139806120 := by
  rw [← show ((([(5844250980341, 1), (8901011109124019, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910479 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_5844250980341, prime_fortyFourAP_8901011109124019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910480 : Nat.totient 52019742900524179770499910480 = 20730526004210674716306493440 := by
  rw [← show ((([(2, 4), (5, 1), (269, 1), (1127981, 1), (2143009765547021929, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910480 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_5, prime_fortyFourAP_269, prime_fortyFourAP_1127981, prime_fortyFourAP_2143009765547021929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910481 : Nat.totient 52019742900524179770499910481 = 34673947672296096442499379840 := by
  rw [← show ((([(3, 3), (5897, 1), (49882515911, 1), (6549753562109, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910481 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3, prime_fortyFourAP_5897, prime_fortyFourAP_49882515911, prime_fortyFourAP_6549753562109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910482 : Nat.totient 52019742900524179770499910482 = 25375132250298557745027609600 := by
  rw [← show ((([(2, 1), (41, 1), (72073, 1), (2285686021, 1), (3850926034597, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910482 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_41, prime_fortyFourAP_72073, prime_fortyFourAP_2285686021, prime_fortyFourAP_3850926034597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910483 : Nat.totient 52019742900524179770499910483 = 51591886119551293081811997696 := by
  rw [← show ((([(127, 1), (2833, 1), (1558243, 1), (27214919, 1), (3409382089, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910483 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_127, prime_fortyFourAP_2833, prime_fortyFourAP_1558243, prime_fortyFourAP_27214919, prime_fortyFourAP_3409382089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910484 : Nat.totient 52019742900524179770499910484 = 14768116268667806427560311680 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (157, 1), (2848589311, 1), (1384711894151563, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910484 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_3, prime_fortyFourAP_7, prime_fortyFourAP_157, prime_fortyFourAP_2848589311, prime_fortyFourAP_1384711894151563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910485 : Nat.totient 52019742900524179770499910485 = 39167755796165140529409024000 := by
  rw [← show ((([(5, 1), (17, 1), (794341, 1), (29796761, 1), (25856708474741, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910485 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_5, prime_fortyFourAP_17, prime_fortyFourAP_794341, prime_fortyFourAP_29796761, prime_fortyFourAP_25856708474741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910486 : Nat.totient 52019742900524179770499910486 = 25404990718486881232535200200 := by
  rw [← show ((([(2, 1), (43, 1), (67971064771, 1), (8899091597863531, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910486 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_43, prime_fortyFourAP_67971064771, prime_fortyFourAP_8899091597863531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910487 : Nat.totient 52019742900524179770499910487 = 33080551086997234940608718432 := by
  rw [← show ((([(3, 1), (29, 1), (83, 1), (7203952762847829908669147, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910487 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3, prime_fortyFourAP_29, prime_fortyFourAP_83, prime_fortyFourAP_7203952762847829908669147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910488 : Nat.totient 52019742900524179770499910488 = 23645337662716489815288244000 := by
  rw [← show ((([(2, 3), (11, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910488 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_11, prime_fortyFourAP_1222615931, prime_fortyFourAP_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910489 : Nat.totient 52019742900524179770499910489 = 51784835098679205140302312320 := by
  rw [← show ((([(367, 1), (563, 1), (50821, 1), (4953937646378557129, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910489 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_367, prime_fortyFourAP_563, prime_fortyFourAP_50821, prime_fortyFourAP_4953937646378557129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910490 : Nat.totient 52019742900524179770499910490 = 13794434616451849533182839776 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (179, 1), (3229034320330489122936059, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910490 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_3, prime_fortyFourAP_5, prime_fortyFourAP_179, prime_fortyFourAP_3229034320330489122936059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910491 : Nat.totient 52019742900524179770499910491 = 41158477899044804509172957088 := by
  rw [← show ((([(7, 1), (13, 1), (151865598659, 1), (3764154169391339, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910491 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_7, prime_fortyFourAP_13, prime_fortyFourAP_151865598659, prime_fortyFourAP_3764154169391339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910492 : Nat.totient 52019742900524179770499910492 = 24855777827226602730477020160 := by
  rw [← show ((([(2, 2), (23, 1), (1307, 1), (5927, 1), (289278289, 1), (252321361381, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910492 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_23, prime_fortyFourAP_1307, prime_fortyFourAP_5927, prime_fortyFourAP_289278289, prime_fortyFourAP_252321361381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910493 : Nat.totient 52019742900524179770499910493 = 33484675421308826129001312240 := by
  rw [← show ((([(3, 1), (31, 1), (439, 1), (1274150510704293231697159, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910493 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3, prime_fortyFourAP_31, prime_fortyFourAP_439, prime_fortyFourAP_1274150510704293231697159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910494 : Nat.totient 52019742900524179770499910494 = 25455283390226096470799008000 := by
  rw [← show ((([(2, 1), (47, 1), (26501, 1), (182279, 1), (294953, 1), (388408415123, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910494 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_47, prime_fortyFourAP_26501, prime_fortyFourAP_182279, prime_fortyFourAP_294953, prime_fortyFourAP_388408415123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910495 : Nat.totient 52019742900524179770499910495 = 38982498073500464430151311360 := by
  rw [← show ((([(5, 1), (19, 1), (89, 1), (4917533, 1), (119861641, 1), (10438235413, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910495 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_5, prime_fortyFourAP_19, prime_fortyFourAP_89, prime_fortyFourAP_4917533, prime_fortyFourAP_119861641, prime_fortyFourAP_10438235413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910496 : Nat.totient 52019742900524179770499910496 = 17339910751052545065487644800 := by
  rw [← show ((([(2, 5), (3, 1), (4885691, 1), (110910068172641332811, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910496 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_3, prime_fortyFourAP_4885691, prime_fortyFourAP_110910068172641332811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910497 : Nat.totient 52019742900524179770499910497 = 52002869808438378868855243156 := by
  rw [← show ((([(3083, 1), (16873092085800901644664259, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910497 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3083, prime_fortyFourAP_16873092085800901644664259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910498 : Nat.totient 52019742900524179770499910498 = 22294175528796077044499961600 := by
  rw [← show ((([(2, 1), (7, 2), (530813703066573262964284801, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910498 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_7, prime_fortyFourAP_530813703066573262964284801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910499 : Nat.totient 52019742900524179770499910499 = 31527116909408593800302976000 := by
  rw [← show ((([(3, 2), (11, 1), (525451948490143230005049601, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910499 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_3, prime_fortyFourAP_11, prime_fortyFourAP_525451948490143230005049601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFourAP_52019742900524179770499910500 : Nat.totient 52019742900524179770499910500 = 20807889426138559564908144000 := by
  rw [← show ((([(2, 2), (5, 3), (2719511, 1), (251922637, 1), (151858876903, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524179770499910500 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFourAP_2, prime_fortyFourAP_5, prime_fortyFourAP_2719511, prime_fortyFourAP_251922637, prime_fortyFourAP_151858876903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FortyFourAP : certifiedKill 1 52019742900524179770499910399 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fortyFourAP_52019742900524179770499910400, phi_fortyFourAP_52019742900524179770499910401, phi_fortyFourAP_52019742900524179770499910402,
    phi_fortyFourAP_52019742900524179770499910403, phi_fortyFourAP_52019742900524179770499910404, phi_fortyFourAP_52019742900524179770499910405,
    phi_fortyFourAP_52019742900524179770499910406, phi_fortyFourAP_52019742900524179770499910407, phi_fortyFourAP_52019742900524179770499910408,
    phi_fortyFourAP_52019742900524179770499910409, phi_fortyFourAP_52019742900524179770499910410, phi_fortyFourAP_52019742900524179770499910411,
    phi_fortyFourAP_52019742900524179770499910412, phi_fortyFourAP_52019742900524179770499910413, phi_fortyFourAP_52019742900524179770499910414,
    phi_fortyFourAP_52019742900524179770499910415, phi_fortyFourAP_52019742900524179770499910416, phi_fortyFourAP_52019742900524179770499910417,
    phi_fortyFourAP_52019742900524179770499910418, phi_fortyFourAP_52019742900524179770499910419, phi_fortyFourAP_52019742900524179770499910420,
    phi_fortyFourAP_52019742900524179770499910421, phi_fortyFourAP_52019742900524179770499910422, phi_fortyFourAP_52019742900524179770499910423,
    phi_fortyFourAP_52019742900524179770499910424, phi_fortyFourAP_52019742900524179770499910425, phi_fortyFourAP_52019742900524179770499910426,
    phi_fortyFourAP_52019742900524179770499910427, phi_fortyFourAP_52019742900524179770499910428, phi_fortyFourAP_52019742900524179770499910429,
    phi_fortyFourAP_52019742900524179770499910430, phi_fortyFourAP_52019742900524179770499910431, phi_fortyFourAP_52019742900524179770499910432,
    phi_fortyFourAP_52019742900524179770499910433, phi_fortyFourAP_52019742900524179770499910434, phi_fortyFourAP_52019742900524179770499910435,
    phi_fortyFourAP_52019742900524179770499910436, phi_fortyFourAP_52019742900524179770499910437, phi_fortyFourAP_52019742900524179770499910438,
    phi_fortyFourAP_52019742900524179770499910439, phi_fortyFourAP_52019742900524179770499910440, phi_fortyFourAP_52019742900524179770499910441,
    phi_fortyFourAP_52019742900524179770499910442, phi_fortyFourAP_52019742900524179770499910443, phi_fortyFourAP_52019742900524179770499910444,
    phi_fortyFourAP_52019742900524179770499910445, phi_fortyFourAP_52019742900524179770499910446, phi_fortyFourAP_52019742900524179770499910447,
    phi_fortyFourAP_52019742900524179770499910448, phi_fortyFourAP_52019742900524179770499910449, phi_fortyFourAP_52019742900524179770499910450,
    phi_fortyFourAP_52019742900524179770499910451, phi_fortyFourAP_52019742900524179770499910452, phi_fortyFourAP_52019742900524179770499910453,
    phi_fortyFourAP_52019742900524179770499910454, phi_fortyFourAP_52019742900524179770499910455, phi_fortyFourAP_52019742900524179770499910456,
    phi_fortyFourAP_52019742900524179770499910457, phi_fortyFourAP_52019742900524179770499910458, phi_fortyFourAP_52019742900524179770499910459,
    phi_fortyFourAP_52019742900524179770499910460, phi_fortyFourAP_52019742900524179770499910461, phi_fortyFourAP_52019742900524179770499910462,
    phi_fortyFourAP_52019742900524179770499910463, phi_fortyFourAP_52019742900524179770499910464, phi_fortyFourAP_52019742900524179770499910465,
    phi_fortyFourAP_52019742900524179770499910466, phi_fortyFourAP_52019742900524179770499910467, phi_fortyFourAP_52019742900524179770499910468,
    phi_fortyFourAP_52019742900524179770499910469, phi_fortyFourAP_52019742900524179770499910470, phi_fortyFourAP_52019742900524179770499910471,
    phi_fortyFourAP_52019742900524179770499910472, phi_fortyFourAP_52019742900524179770499910473, phi_fortyFourAP_52019742900524179770499910474,
    phi_fortyFourAP_52019742900524179770499910475, phi_fortyFourAP_52019742900524179770499910476, phi_fortyFourAP_52019742900524179770499910477,
    phi_fortyFourAP_52019742900524179770499910478, phi_fortyFourAP_52019742900524179770499910479, phi_fortyFourAP_52019742900524179770499910480,
    phi_fortyFourAP_52019742900524179770499910481, phi_fortyFourAP_52019742900524179770499910482, phi_fortyFourAP_52019742900524179770499910483,
    phi_fortyFourAP_52019742900524179770499910484, phi_fortyFourAP_52019742900524179770499910485, phi_fortyFourAP_52019742900524179770499910486,
    phi_fortyFourAP_52019742900524179770499910487, phi_fortyFourAP_52019742900524179770499910488, phi_fortyFourAP_52019742900524179770499910489,
    phi_fortyFourAP_52019742900524179770499910490, phi_fortyFourAP_52019742900524179770499910491, phi_fortyFourAP_52019742900524179770499910492,
    phi_fortyFourAP_52019742900524179770499910493, phi_fortyFourAP_52019742900524179770499910494, phi_fortyFourAP_52019742900524179770499910495,
    phi_fortyFourAP_52019742900524179770499910496, phi_fortyFourAP_52019742900524179770499910497, phi_fortyFourAP_52019742900524179770499910498,
    phi_fortyFourAP_52019742900524179770499910499, phi_fortyFourAP_52019742900524179770499910500]

end TotientTailPeriodKiller
end Erdos249257
