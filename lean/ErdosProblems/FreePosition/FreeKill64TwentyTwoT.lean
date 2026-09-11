import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def twentyTwoTFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem twentyTwoTFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    twentyTwoTFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [twentyTwoTFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [twentyTwoTFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then twentyTwoTFastPow a n * twentyTwoTFastPow a n * a
        else twentyTwoTFastPow a n * twentyTwoTFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_twentyTwoT_2 : Nat.Prime 2 := by norm_num
private theorem prime_twentyTwoT_3 : Nat.Prime 3 := by norm_num
private theorem prime_twentyTwoT_5 : Nat.Prime 5 := by norm_num
private theorem prime_twentyTwoT_7 : Nat.Prime 7 := by norm_num
private theorem prime_twentyTwoT_11 : Nat.Prime 11 := by norm_num
private theorem prime_twentyTwoT_13 : Nat.Prime 13 := by norm_num
private theorem prime_twentyTwoT_17 : Nat.Prime 17 := by norm_num
private theorem prime_twentyTwoT_19 : Nat.Prime 19 := by norm_num
private theorem prime_twentyTwoT_23 : Nat.Prime 23 := by norm_num
private theorem prime_twentyTwoT_29 : Nat.Prime 29 := by norm_num
private theorem prime_twentyTwoT_31 : Nat.Prime 31 := by norm_num
private theorem prime_twentyTwoT_37 : Nat.Prime 37 := by norm_num
private theorem prime_twentyTwoT_41 : Nat.Prime 41 := by norm_num
private theorem prime_twentyTwoT_43 : Nat.Prime 43 := by norm_num
private theorem prime_twentyTwoT_47 : Nat.Prime 47 := by norm_num
private theorem prime_twentyTwoT_53 : Nat.Prime 53 := by norm_num
private theorem prime_twentyTwoT_59 : Nat.Prime 59 := by norm_num
private theorem prime_twentyTwoT_61 : Nat.Prime 61 := by norm_num
private theorem prime_twentyTwoT_67 : Nat.Prime 67 := by norm_num
private theorem prime_twentyTwoT_71 : Nat.Prime 71 := by norm_num
private theorem prime_twentyTwoT_73 : Nat.Prime 73 := by norm_num
private theorem prime_twentyTwoT_79 : Nat.Prime 79 := by norm_num
private theorem prime_twentyTwoT_83 : Nat.Prime 83 := by norm_num
private theorem prime_twentyTwoT_89 : Nat.Prime 89 := by norm_num
private theorem prime_twentyTwoT_97 : Nat.Prime 97 := by norm_num
private theorem prime_twentyTwoT_101 : Nat.Prime 101 := by norm_num
private theorem prime_twentyTwoT_103 : Nat.Prime 103 := by norm_num
private theorem prime_twentyTwoT_107 : Nat.Prime 107 := by norm_num
private theorem prime_twentyTwoT_109 : Nat.Prime 109 := by norm_num
private theorem prime_twentyTwoT_113 : Nat.Prime 113 := by norm_num
private theorem prime_twentyTwoT_127 : Nat.Prime 127 := by norm_num
private theorem prime_twentyTwoT_131 : Nat.Prime 131 := by norm_num
private theorem prime_twentyTwoT_137 : Nat.Prime 137 := by norm_num
private theorem prime_twentyTwoT_139 : Nat.Prime 139 := by norm_num
private theorem prime_twentyTwoT_149 : Nat.Prime 149 := by norm_num
private theorem prime_twentyTwoT_151 : Nat.Prime 151 := by norm_num
private theorem prime_twentyTwoT_157 : Nat.Prime 157 := by norm_num
private theorem prime_twentyTwoT_163 : Nat.Prime 163 := by norm_num
private theorem prime_twentyTwoT_167 : Nat.Prime 167 := by norm_num
private theorem prime_twentyTwoT_173 : Nat.Prime 173 := by norm_num
private theorem prime_twentyTwoT_179 : Nat.Prime 179 := by norm_num
private theorem prime_twentyTwoT_181 : Nat.Prime 181 := by norm_num
private theorem prime_twentyTwoT_191 : Nat.Prime 191 := by norm_num
private theorem prime_twentyTwoT_199 : Nat.Prime 199 := by norm_num
private theorem prime_twentyTwoT_211 : Nat.Prime 211 := by norm_num
private theorem prime_twentyTwoT_223 : Nat.Prime 223 := by norm_num
private theorem prime_twentyTwoT_227 : Nat.Prime 227 := by norm_num
private theorem prime_twentyTwoT_233 : Nat.Prime 233 := by norm_num
private theorem prime_twentyTwoT_239 : Nat.Prime 239 := by norm_num
private theorem prime_twentyTwoT_241 : Nat.Prime 241 := by norm_num
private theorem prime_twentyTwoT_257 : Nat.Prime 257 := by norm_num
private theorem prime_twentyTwoT_263 : Nat.Prime 263 := by norm_num
private theorem prime_twentyTwoT_269 : Nat.Prime 269 := by norm_num
private theorem prime_twentyTwoT_271 : Nat.Prime 271 := by norm_num
private theorem prime_twentyTwoT_277 : Nat.Prime 277 := by norm_num
private theorem prime_twentyTwoT_283 : Nat.Prime 283 := by norm_num
private theorem prime_twentyTwoT_293 : Nat.Prime 293 := by norm_num
private theorem prime_twentyTwoT_311 : Nat.Prime 311 := by norm_num
private theorem prime_twentyTwoT_313 : Nat.Prime 313 := by norm_num
private theorem prime_twentyTwoT_331 : Nat.Prime 331 := by norm_num
private theorem prime_twentyTwoT_337 : Nat.Prime 337 := by norm_num
private theorem prime_twentyTwoT_347 : Nat.Prime 347 := by norm_num
private theorem prime_twentyTwoT_353 : Nat.Prime 353 := by norm_num
private theorem prime_twentyTwoT_379 : Nat.Prime 379 := by norm_num
private theorem prime_twentyTwoT_383 : Nat.Prime 383 := by norm_num
private theorem prime_twentyTwoT_397 : Nat.Prime 397 := by norm_num
private theorem prime_twentyTwoT_401 : Nat.Prime 401 := by norm_num
private theorem prime_twentyTwoT_409 : Nat.Prime 409 := by norm_num
private theorem prime_twentyTwoT_421 : Nat.Prime 421 := by norm_num
private theorem prime_twentyTwoT_433 : Nat.Prime 433 := by norm_num
private theorem prime_twentyTwoT_439 : Nat.Prime 439 := by norm_num
private theorem prime_twentyTwoT_467 : Nat.Prime 467 := by norm_num
private theorem prime_twentyTwoT_479 : Nat.Prime 479 := by norm_num
private theorem prime_twentyTwoT_491 : Nat.Prime 491 := by norm_num
private theorem prime_twentyTwoT_557 : Nat.Prime 557 := by norm_num
private theorem prime_twentyTwoT_593 : Nat.Prime 593 := by norm_num
private theorem prime_twentyTwoT_599 : Nat.Prime 599 := by norm_num
private theorem prime_twentyTwoT_631 : Nat.Prime 631 := by norm_num
private theorem prime_twentyTwoT_641 : Nat.Prime 641 := by norm_num
private theorem prime_twentyTwoT_643 : Nat.Prime 643 := by norm_num
private theorem prime_twentyTwoT_647 : Nat.Prime 647 := by norm_num
private theorem prime_twentyTwoT_653 : Nat.Prime 653 := by norm_num
private theorem prime_twentyTwoT_661 : Nat.Prime 661 := by norm_num
private theorem prime_twentyTwoT_719 : Nat.Prime 719 := by norm_num
private theorem prime_twentyTwoT_727 : Nat.Prime 727 := by norm_num
private theorem prime_twentyTwoT_739 : Nat.Prime 739 := by norm_num
private theorem prime_twentyTwoT_757 : Nat.Prime 757 := by norm_num
private theorem prime_twentyTwoT_797 : Nat.Prime 797 := by norm_num
private theorem prime_twentyTwoT_811 : Nat.Prime 811 := by norm_num
private theorem prime_twentyTwoT_827 : Nat.Prime 827 := by norm_num
private theorem prime_twentyTwoT_853 : Nat.Prime 853 := by norm_num
private theorem prime_twentyTwoT_857 : Nat.Prime 857 := by norm_num
private theorem prime_twentyTwoT_911 : Nat.Prime 911 := by norm_num
private theorem prime_twentyTwoT_941 : Nat.Prime 941 := by norm_num
private theorem prime_twentyTwoT_947 : Nat.Prime 947 := by norm_num
private theorem prime_twentyTwoT_967 : Nat.Prime 967 := by norm_num
private theorem prime_twentyTwoT_977 : Nat.Prime 977 := by norm_num
private theorem prime_twentyTwoT_983 : Nat.Prime 983 := by norm_num
private theorem prime_twentyTwoT_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_twentyTwoT_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_twentyTwoT_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_twentyTwoT_1039 : Nat.Prime 1039 := by norm_num
private theorem prime_twentyTwoT_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_twentyTwoT_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_twentyTwoT_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_twentyTwoT_1129 : Nat.Prime 1129 := by norm_num
private theorem prime_twentyTwoT_1181 : Nat.Prime 1181 := by norm_num
private theorem prime_twentyTwoT_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_twentyTwoT_1217 : Nat.Prime 1217 := by norm_num
private theorem prime_twentyTwoT_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_twentyTwoT_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_twentyTwoT_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_twentyTwoT_1291 : Nat.Prime 1291 := by norm_num
private theorem prime_twentyTwoT_1297 : Nat.Prime 1297 := by norm_num
private theorem prime_twentyTwoT_1307 : Nat.Prime 1307 := by norm_num
private theorem prime_twentyTwoT_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_twentyTwoT_1381 : Nat.Prime 1381 := by norm_num
private theorem prime_twentyTwoT_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_twentyTwoT_1523 : Nat.Prime 1523 := by norm_num
private theorem prime_twentyTwoT_1553 : Nat.Prime 1553 := by norm_num
private theorem prime_twentyTwoT_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_twentyTwoT_1597 : Nat.Prime 1597 := by norm_num
private theorem prime_twentyTwoT_1627 : Nat.Prime 1627 := by norm_num
private theorem prime_twentyTwoT_1637 : Nat.Prime 1637 := by norm_num
private theorem prime_twentyTwoT_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_twentyTwoT_1697 : Nat.Prime 1697 := by norm_num
private theorem prime_twentyTwoT_1709 : Nat.Prime 1709 := by norm_num
private theorem prime_twentyTwoT_1753 : Nat.Prime 1753 := by norm_num
private theorem prime_twentyTwoT_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_twentyTwoT_2081 : Nat.Prime 2081 := by norm_num
private theorem prime_twentyTwoT_2113 : Nat.Prime 2113 := by norm_num
private theorem prime_twentyTwoT_2129 : Nat.Prime 2129 := by norm_num
private theorem prime_twentyTwoT_2161 : Nat.Prime 2161 := by norm_num
private theorem prime_twentyTwoT_2203 : Nat.Prime 2203 := by norm_num
private theorem prime_twentyTwoT_2311 : Nat.Prime 2311 := by norm_num
private theorem prime_twentyTwoT_2339 : Nat.Prime 2339 := by norm_num
private theorem prime_twentyTwoT_2341 : Nat.Prime 2341 := by norm_num
private theorem prime_twentyTwoT_2351 : Nat.Prime 2351 := by norm_num
private theorem prime_twentyTwoT_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_twentyTwoT_2551 : Nat.Prime 2551 := by norm_num
private theorem prime_twentyTwoT_2557 : Nat.Prime 2557 := by norm_num
private theorem prime_twentyTwoT_2753 : Nat.Prime 2753 := by norm_num
private theorem prime_twentyTwoT_2819 : Nat.Prime 2819 := by norm_num
private theorem prime_twentyTwoT_2861 : Nat.Prime 2861 := by norm_num
private theorem prime_twentyTwoT_2887 : Nat.Prime 2887 := by norm_num
private theorem prime_twentyTwoT_3011 : Nat.Prime 3011 := by norm_num
private theorem prime_twentyTwoT_3041 : Nat.Prime 3041 := by norm_num
private theorem prime_twentyTwoT_3203 : Nat.Prime 3203 := by norm_num
private theorem prime_twentyTwoT_3221 : Nat.Prime 3221 := by norm_num
private theorem prime_twentyTwoT_3251 : Nat.Prime 3251 := by norm_num
private theorem prime_twentyTwoT_3343 : Nat.Prime 3343 := by norm_num
private theorem prime_twentyTwoT_3559 : Nat.Prime 3559 := by norm_num
private theorem prime_twentyTwoT_3673 : Nat.Prime 3673 := by norm_num
private theorem prime_twentyTwoT_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_twentyTwoT_3769 : Nat.Prime 3769 := by norm_num
private theorem prime_twentyTwoT_3793 : Nat.Prime 3793 := by norm_num
private theorem prime_twentyTwoT_3803 : Nat.Prime 3803 := by norm_num
private theorem prime_twentyTwoT_3847 : Nat.Prime 3847 := by norm_num
private theorem prime_twentyTwoT_3907 : Nat.Prime 3907 := by norm_num
private theorem prime_twentyTwoT_4051 : Nat.Prime 4051 := by norm_num
private theorem prime_twentyTwoT_4093 : Nat.Prime 4093 := by norm_num
private theorem prime_twentyTwoT_4211 : Nat.Prime 4211 := by norm_num
private theorem prime_twentyTwoT_4231 : Nat.Prime 4231 := by norm_num
private theorem prime_twentyTwoT_4259 : Nat.Prime 4259 := by norm_num
private theorem prime_twentyTwoT_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_twentyTwoT_4337 : Nat.Prime 4337 := by norm_num
private theorem prime_twentyTwoT_4339 : Nat.Prime 4339 := by norm_num
private theorem prime_twentyTwoT_4457 : Nat.Prime 4457 := by norm_num
private theorem prime_twentyTwoT_4493 : Nat.Prime 4493 := by norm_num
private theorem prime_twentyTwoT_4549 : Nat.Prime 4549 := by norm_num
private theorem prime_twentyTwoT_4663 : Nat.Prime 4663 := by norm_num
private theorem prime_twentyTwoT_4691 : Nat.Prime 4691 := by norm_num
private theorem prime_twentyTwoT_4721 : Nat.Prime 4721 := by norm_num
private theorem prime_twentyTwoT_4937 : Nat.Prime 4937 := by norm_num
private theorem prime_twentyTwoT_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_twentyTwoT_5051 : Nat.Prime 5051 := by norm_num
private theorem prime_twentyTwoT_5417 : Nat.Prime 5417 := by norm_num
private theorem prime_twentyTwoT_5441 : Nat.Prime 5441 := by norm_num
private theorem prime_twentyTwoT_5449 : Nat.Prime 5449 := by norm_num
private theorem prime_twentyTwoT_5639 : Nat.Prime 5639 := by norm_num
private theorem prime_twentyTwoT_5843 : Nat.Prime 5843 := by norm_num
private theorem prime_twentyTwoT_5869 : Nat.Prime 5869 := by norm_num
private theorem prime_twentyTwoT_5927 : Nat.Prime 5927 := by norm_num
private theorem prime_twentyTwoT_6079 : Nat.Prime 6079 := by norm_num
private theorem prime_twentyTwoT_6133 : Nat.Prime 6133 := by norm_num
private theorem prime_twentyTwoT_6269 : Nat.Prime 6269 := by norm_num
private theorem prime_twentyTwoT_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_twentyTwoT_6379 : Nat.Prime 6379 := by norm_num
private theorem prime_twentyTwoT_6529 : Nat.Prime 6529 := by norm_num
private theorem prime_twentyTwoT_6599 : Nat.Prime 6599 := by norm_num
private theorem prime_twentyTwoT_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_twentyTwoT_6899 : Nat.Prime 6899 := by norm_num
private theorem prime_twentyTwoT_7013 : Nat.Prime 7013 := by norm_num
private theorem prime_twentyTwoT_7039 : Nat.Prime 7039 := by norm_num
private theorem prime_twentyTwoT_7457 : Nat.Prime 7457 := by norm_num
private theorem prime_twentyTwoT_7723 : Nat.Prime 7723 := by norm_num
private theorem prime_twentyTwoT_7867 : Nat.Prime 7867 := by norm_num
private theorem prime_twentyTwoT_8147 : Nat.Prime 8147 := by norm_num
private theorem prime_twentyTwoT_8623 : Nat.Prime 8623 := by norm_num
private theorem prime_twentyTwoT_8669 : Nat.Prime 8669 := by norm_num
private theorem prime_twentyTwoT_8951 : Nat.Prime 8951 := by norm_num
private theorem prime_twentyTwoT_8971 : Nat.Prime 8971 := by norm_num
private theorem prime_twentyTwoT_9103 : Nat.Prime 9103 := by norm_num
private theorem prime_twentyTwoT_9257 : Nat.Prime 9257 := by norm_num
private theorem prime_twentyTwoT_9619 : Nat.Prime 9619 := by norm_num
private theorem prime_twentyTwoT_9721 : Nat.Prime 9721 := by norm_num
private theorem prime_twentyTwoT_10159 : Nat.Prime 10159 := by norm_num
private theorem prime_twentyTwoT_10691 : Nat.Prime 10691 := by norm_num
private theorem prime_twentyTwoT_10903 : Nat.Prime 10903 := by norm_num
private theorem prime_twentyTwoT_10987 : Nat.Prime 10987 := by norm_num
private theorem prime_twentyTwoT_11827 : Nat.Prime 11827 := by norm_num
private theorem prime_twentyTwoT_11933 : Nat.Prime 11933 := by norm_num
private theorem prime_twentyTwoT_11987 : Nat.Prime 11987 := by norm_num
private theorem prime_twentyTwoT_12227 : Nat.Prime 12227 := by norm_num
private theorem prime_twentyTwoT_12721 : Nat.Prime 12721 := by norm_num
private theorem prime_twentyTwoT_12743 : Nat.Prime 12743 := by norm_num
private theorem prime_twentyTwoT_13163 : Nat.Prime 13163 := by norm_num
private theorem prime_twentyTwoT_13183 : Nat.Prime 13183 := by norm_num
private theorem prime_twentyTwoT_14423 : Nat.Prime 14423 := by norm_num
private theorem prime_twentyTwoT_15991 : Nat.Prime 15991 := by norm_num
private theorem prime_twentyTwoT_16073 : Nat.Prime 16073 := by norm_num
private theorem prime_twentyTwoT_16987 : Nat.Prime 16987 := by norm_num
private theorem prime_twentyTwoT_17011 : Nat.Prime 17011 := by norm_num
private theorem prime_twentyTwoT_17749 : Nat.Prime 17749 := by norm_num
private theorem prime_twentyTwoT_18077 : Nat.Prime 18077 := by norm_num
private theorem prime_twentyTwoT_18131 : Nat.Prime 18131 := by norm_num
private theorem prime_twentyTwoT_18217 : Nat.Prime 18217 := by norm_num
private theorem prime_twentyTwoT_19553 : Nat.Prime 19553 := by norm_num
private theorem prime_twentyTwoT_19841 : Nat.Prime 19841 := by norm_num
private theorem prime_twentyTwoT_20269 : Nat.Prime 20269 := by norm_num
private theorem prime_twentyTwoT_22511 : Nat.Prime 22511 := by norm_num
private theorem prime_twentyTwoT_23447 : Nat.Prime 23447 := by norm_num
private theorem prime_twentyTwoT_25439 : Nat.Prime 25439 := by norm_num
private theorem prime_twentyTwoT_26501 : Nat.Prime 26501 := by norm_num
private theorem prime_twentyTwoT_27077 : Nat.Prime 27077 := by norm_num
private theorem prime_twentyTwoT_27361 : Nat.Prime 27361 := by norm_num
private theorem prime_twentyTwoT_28351 : Nat.Prime 28351 := by norm_num
private theorem prime_twentyTwoT_28687 : Nat.Prime 28687 := by norm_num
private theorem prime_twentyTwoT_28807 : Nat.Prime 28807 := by norm_num
private theorem prime_twentyTwoT_29131 : Nat.Prime 29131 := by norm_num
private theorem prime_twentyTwoT_29873 : Nat.Prime 29873 := by norm_num
private theorem prime_twentyTwoT_31159 : Nat.Prime 31159 := by norm_num
private theorem prime_twentyTwoT_31873 : Nat.Prime 31873 := by norm_num
private theorem prime_twentyTwoT_32503 : Nat.Prime 32503 := by norm_num
private theorem prime_twentyTwoT_32531 : Nat.Prime 32531 := by norm_num
private theorem prime_twentyTwoT_32843 : Nat.Prime 32843 := by norm_num
private theorem prime_twentyTwoT_32869 : Nat.Prime 32869 := by norm_num
private theorem prime_twentyTwoT_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_twentyTwoT_35509 : Nat.Prime 35509 := by norm_num
private theorem prime_twentyTwoT_35543 : Nat.Prime 35543 := by norm_num
private theorem prime_twentyTwoT_35569 : Nat.Prime 35569 := by norm_num
private theorem prime_twentyTwoT_36899 : Nat.Prime 36899 := by norm_num
private theorem prime_twentyTwoT_36973 : Nat.Prime 36973 := by norm_num
private theorem prime_twentyTwoT_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_twentyTwoT_37889 : Nat.Prime 37889 := by norm_num
private theorem prime_twentyTwoT_37967 : Nat.Prime 37967 := by norm_num
private theorem prime_twentyTwoT_38047 : Nat.Prime 38047 := by norm_num
private theorem prime_twentyTwoT_39113 : Nat.Prime 39113 := by norm_num
private theorem prime_twentyTwoT_40627 : Nat.Prime 40627 := by norm_num
private theorem prime_twentyTwoT_43427 : Nat.Prime 43427 := by norm_num
private theorem prime_twentyTwoT_43891 : Nat.Prime 43891 := by norm_num
private theorem prime_twentyTwoT_47659 : Nat.Prime 47659 := by norm_num
private theorem prime_twentyTwoT_48091 : Nat.Prime 48091 := by norm_num
private theorem prime_twentyTwoT_50411 : Nat.Prime 50411 := by norm_num
private theorem prime_twentyTwoT_51593 : Nat.Prime 51593 := by norm_num
private theorem prime_twentyTwoT_55733 : Nat.Prime 55733 := by norm_num
private theorem prime_twentyTwoT_58199 : Nat.Prime 58199 := by norm_num
private theorem prime_twentyTwoT_59159 : Nat.Prime 59159 := by norm_num
private theorem prime_twentyTwoT_60353 : Nat.Prime 60353 := by norm_num
private theorem prime_twentyTwoT_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_twentyTwoT_66751 : Nat.Prime 66751 := by norm_num
private theorem prime_twentyTwoT_67121 : Nat.Prime 67121 := by norm_num
private theorem prime_twentyTwoT_67399 : Nat.Prime 67399 := by norm_num
private theorem prime_twentyTwoT_67901 : Nat.Prime 67901 := by norm_num
private theorem prime_twentyTwoT_72073 : Nat.Prime 72073 := by norm_num
private theorem prime_twentyTwoT_72907 : Nat.Prime 72907 := by norm_num
private theorem prime_twentyTwoT_73141 : Nat.Prime 73141 := by norm_num
private theorem prime_twentyTwoT_74201 : Nat.Prime 74201 := by norm_num
private theorem prime_twentyTwoT_74687 : Nat.Prime 74687 := by norm_num
private theorem prime_twentyTwoT_78401 : Nat.Prime 78401 := by norm_num
private theorem prime_twentyTwoT_85889 : Nat.Prime 85889 := by norm_num
private theorem prime_twentyTwoT_89669 : Nat.Prime 89669 := by norm_num
private theorem prime_twentyTwoT_97523 : Nat.Prime 97523 := by norm_num
private theorem prime_twentyTwoT_97849 : Nat.Prime 97849 := by norm_num
private theorem prime_twentyTwoT_101267 : Nat.Prime 101267 := by norm_num
private theorem prime_twentyTwoT_101363 : Nat.Prime 101363 := by norm_num
private theorem prime_twentyTwoT_102953 : Nat.Prime 102953 := by norm_num
private theorem prime_twentyTwoT_104053 : Nat.Prime 104053 := by norm_num
private theorem prime_twentyTwoT_113363 : Nat.Prime 113363 := by norm_num
private theorem prime_twentyTwoT_117193 : Nat.Prime 117193 := by norm_num
private theorem prime_twentyTwoT_118373 : Nat.Prime 118373 := by norm_num
private theorem prime_twentyTwoT_123923 : Nat.Prime 123923 := by norm_num
private theorem prime_twentyTwoT_129281 : Nat.Prime 129281 := by norm_num
private theorem prime_twentyTwoT_130021 : Nat.Prime 130021 := by norm_num
private theorem prime_twentyTwoT_130073 : Nat.Prime 130073 := by norm_num
private theorem prime_twentyTwoT_132857 : Nat.Prime 132857 := by norm_num
private theorem prime_twentyTwoT_147163 : Nat.Prime 147163 := by norm_num
private theorem prime_twentyTwoT_152041 : Nat.Prime 152041 := by norm_num
private theorem prime_twentyTwoT_154807 : Nat.Prime 154807 := by norm_num
private theorem prime_twentyTwoT_159671 : Nat.Prime 159671 := by norm_num
private theorem prime_twentyTwoT_174157 : Nat.Prime 174157 := by norm_num
private theorem prime_twentyTwoT_182279 : Nat.Prime 182279 := by norm_num
private theorem prime_twentyTwoT_186871 : Nat.Prime 186871 := by norm_num
private theorem prime_twentyTwoT_189529 : Nat.Prime 189529 := by norm_num
private theorem prime_twentyTwoT_198251 : Nat.Prime 198251 := by norm_num
private theorem prime_twentyTwoT_205253 : Nat.Prime 205253 := by norm_num
private theorem prime_twentyTwoT_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_twentyTwoT_222419 : Nat.Prime 222419 := by norm_num
private theorem prime_twentyTwoT_225581 : Nat.Prime 225581 := by norm_num
private theorem prime_twentyTwoT_246223 : Nat.Prime 246223 := by norm_num
private theorem prime_twentyTwoT_254213 : Nat.Prime 254213 := by norm_num
private theorem prime_twentyTwoT_259621 : Nat.Prime 259621 := by norm_num
private theorem prime_twentyTwoT_272887 : Nat.Prime 272887 := by norm_num
private theorem prime_twentyTwoT_274357 : Nat.Prime 274357 := by norm_num
private theorem prime_twentyTwoT_282959 : Nat.Prime 282959 := by norm_num
private theorem prime_twentyTwoT_294953 : Nat.Prime 294953 := by norm_num
private theorem prime_twentyTwoT_299969 : Nat.Prime 299969 := by norm_num
private theorem prime_twentyTwoT_316363 : Nat.Prime 316363 := by norm_num
private theorem prime_twentyTwoT_320027 : Nat.Prime 320027 := by norm_num
private theorem prime_twentyTwoT_358993 : Nat.Prime 358993 := by norm_num
private theorem prime_twentyTwoT_373297 : Nat.Prime 373297 := by norm_num
private theorem prime_twentyTwoT_385327 : Nat.Prime 385327 := by norm_num
private theorem prime_twentyTwoT_432391 : Nat.Prime 432391 := by norm_num
private theorem prime_twentyTwoT_432743 : Nat.Prime 432743 := by norm_num
private theorem prime_twentyTwoT_455471 : Nat.Prime 455471 := by norm_num
private theorem prime_twentyTwoT_470579 : Nat.Prime 470579 := by norm_num
private theorem prime_twentyTwoT_512047 : Nat.Prime 512047 := by norm_num
private theorem prime_twentyTwoT_514793 : Nat.Prime 514793 := by norm_num
private theorem prime_twentyTwoT_565567 : Nat.Prime 565567 := by norm_num
private theorem prime_twentyTwoT_624277 : Nat.Prime 624277 := by norm_num
private theorem prime_twentyTwoT_627787 : Nat.Prime 627787 := by norm_num
private theorem prime_twentyTwoT_631361 : Nat.Prime 631361 := by norm_num
private theorem prime_twentyTwoT_683819 : Nat.Prime 683819 := by norm_num
private theorem prime_twentyTwoT_706841 : Nat.Prime 706841 := by norm_num
private theorem prime_twentyTwoT_727781 : Nat.Prime 727781 := by norm_num
private theorem prime_twentyTwoT_760321 : Nat.Prime 760321 := by norm_num
private theorem prime_twentyTwoT_776813 : Nat.Prime 776813 := by norm_num
private theorem prime_twentyTwoT_796447 : Nat.Prime 796447 := by norm_num
private theorem prime_twentyTwoT_810913 : Nat.Prime 810913 := by norm_num
private theorem prime_twentyTwoT_814829 : Nat.Prime 814829 := by norm_num
private theorem prime_twentyTwoT_834527 : Nat.Prime 834527 := by norm_num
private theorem prime_twentyTwoT_895529 : Nat.Prime 895529 := by norm_num
private theorem prime_twentyTwoT_940573 : Nat.Prime 940573 := by norm_num
private theorem prime_twentyTwoT_1079527 : Nat.Prime 1079527 := by norm_num
private theorem prime_twentyTwoT_1098233 : Nat.Prime 1098233 := by norm_num
private theorem prime_twentyTwoT_1127981 : Nat.Prime 1127981 := by norm_num
private theorem prime_twentyTwoT_1142021 : Nat.Prime 1142021 := by norm_num
private theorem prime_twentyTwoT_1179991 : Nat.Prime 1179991 := by norm_num
private theorem prime_twentyTwoT_1214459 : Nat.Prime 1214459 := by norm_num
private theorem prime_twentyTwoT_1231171 : Nat.Prime 1231171 := by norm_num
private theorem prime_twentyTwoT_1279601 : Nat.Prime 1279601 := by norm_num
private theorem prime_twentyTwoT_1304419 : Nat.Prime 1304419 := by norm_num
private theorem prime_twentyTwoT_1309753 : Nat.Prime 1309753 := by norm_num
private theorem prime_twentyTwoT_1358821 : Nat.Prime 1358821 := by norm_num
private theorem prime_twentyTwoT_1454477 : Nat.Prime 1454477 := by norm_num
private theorem prime_twentyTwoT_1470233 : Nat.Prime 1470233 := by norm_num
private theorem prime_twentyTwoT_1674623 : Nat.Prime 1674623 := by norm_num
private theorem prime_twentyTwoT_1849103 : Nat.Prime 1849103 := by norm_num
private theorem prime_twentyTwoT_1883407 : Nat.Prime 1883407 := by norm_num
private theorem prime_twentyTwoT_1899647 : Nat.Prime 1899647 := by norm_num
private theorem prime_twentyTwoT_2029241 : Nat.Prime 2029241 := by norm_num
private theorem prime_twentyTwoT_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_twentyTwoT_2095699 : Nat.Prime 2095699 := by norm_num
private theorem prime_twentyTwoT_2367523 : Nat.Prime 2367523 := by norm_num
private theorem prime_twentyTwoT_2395051 : Nat.Prime 2395051 := by norm_num
private theorem prime_twentyTwoT_2466931 : Nat.Prime 2466931 := by norm_num
private theorem prime_twentyTwoT_2502833 : Nat.Prime 2502833 := by norm_num
private theorem prime_twentyTwoT_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_twentyTwoT_2594677 : Nat.Prime 2594677 := by norm_num
private theorem prime_twentyTwoT_2719511 : Nat.Prime 2719511 := by norm_num
private theorem prime_twentyTwoT_2864723 : Nat.Prime 2864723 := by norm_num
private theorem prime_twentyTwoT_2953667 : Nat.Prime 2953667 := by norm_num
private theorem prime_twentyTwoT_3022027 : Nat.Prime 3022027 := by norm_num
private theorem prime_twentyTwoT_3072847 : Nat.Prime 3072847 := by norm_num
private theorem prime_twentyTwoT_3274511 : Nat.Prime 3274511 := by norm_num
private theorem prime_twentyTwoT_3446959 : Nat.Prime 3446959 := by norm_num
private theorem prime_twentyTwoT_3707213 : Nat.Prime 3707213 := by norm_num
private theorem prime_twentyTwoT_3762667 : Nat.Prime 3762667 := by norm_num
private theorem prime_twentyTwoT_4581677 : Nat.Prime 4581677 := by norm_num
private theorem prime_twentyTwoT_4663859 : Nat.Prime 4663859 := by norm_num
private theorem prime_twentyTwoT_4725683 : Nat.Prime 4725683 := by norm_num
private theorem prime_twentyTwoT_4868909 : Nat.Prime 4868909 := by norm_num
private theorem prime_twentyTwoT_4885691 : Nat.Prime 4885691 := by norm_num
private theorem prime_twentyTwoT_4938853 : Nat.Prime 4938853 := by norm_num
private theorem prime_twentyTwoT_5131963 : Nat.Prime 5131963 := by norm_num
private theorem prime_twentyTwoT_5191799 : Nat.Prime 5191799 := by norm_num
private theorem prime_twentyTwoT_5225593 : Nat.Prime 5225593 := by norm_num
private theorem prime_twentyTwoT_5339791 : Nat.Prime 5339791 := by norm_num
private theorem prime_twentyTwoT_5426387 : Nat.Prime 5426387 := by norm_num
private theorem prime_twentyTwoT_5826967 : Nat.Prime 5826967 := by norm_num
private theorem prime_twentyTwoT_6411467 : Nat.Prime 6411467 := by norm_num
private theorem prime_twentyTwoT_6672769 : Nat.Prime 6672769 := by norm_num
private theorem prime_twentyTwoT_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_twentyTwoT_8917991 : Nat.Prime 8917991 := by norm_num
private theorem prime_twentyTwoT_9392503 : Nat.Prime 9392503 := by norm_num
private theorem prime_twentyTwoT_9492089 : Nat.Prime 9492089 := by norm_num
private theorem prime_twentyTwoT_10269137 : Nat.Prime 10269137 := by norm_num
private theorem prime_twentyTwoT_10459727 : Nat.Prime 10459727 := by norm_num
private theorem prime_twentyTwoT_10692109 : Nat.Prime 10692109 := by norm_num
private theorem prime_twentyTwoT_11068193 : Nat.Prime 11068193 := by norm_num
private theorem prime_twentyTwoT_11218483 : Nat.Prime 11218483 := by norm_num
private theorem prime_twentyTwoT_11503777 : Nat.Prime 11503777 := by norm_num
private theorem prime_twentyTwoT_11540831 : Nat.Prime 11540831 := by norm_num
private theorem prime_twentyTwoT_12383491 : Nat.Prime 12383491 := by norm_num
private theorem prime_twentyTwoT_12705349 : Nat.Prime 12705349 := by norm_num
private theorem prime_twentyTwoT_14329009 : Nat.Prime 14329009 := by norm_num
private theorem prime_twentyTwoT_14681717 : Nat.Prime 14681717 := by norm_num
private theorem prime_twentyTwoT_17570123 : Nat.Prime 17570123 := by norm_num
private theorem prime_twentyTwoT_19773451 : Nat.Prime 19773451 := by norm_num
private theorem prime_twentyTwoT_19804481 : Nat.Prime 19804481 := by norm_num
private theorem prime_twentyTwoT_20930737 : Nat.Prime 20930737 := by norm_num
private theorem prime_twentyTwoT_21160721 : Nat.Prime 21160721 := by norm_num
private theorem prime_twentyTwoT_22140787 : Nat.Prime 22140787 := by norm_num
private theorem prime_twentyTwoT_24507097 : Nat.Prime 24507097 := by norm_num
private theorem prime_twentyTwoT_24608981 : Nat.Prime 24608981 := by norm_num
private theorem prime_twentyTwoT_25824109 : Nat.Prime 25824109 := by norm_num
private theorem prime_twentyTwoT_28231919 : Nat.Prime 28231919 := by norm_num
private theorem prime_twentyTwoT_28617707 : Nat.Prime 28617707 := by norm_num
private theorem prime_twentyTwoT_29602789 : Nat.Prime 29602789 := by norm_num

private theorem prime_twentyTwoT_33026989 : Nat.Prime 33026989 := by
  apply lucas_primality 33026989 (6 : ZMod 33026989)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (23, 1), (7039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (23, 1), (7039, 1)] : List FactorBlock).map factorBlockValue).prod) = 33026989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_17
      · exact prime_twentyTwoT_23
      · exact prime_twentyTwoT_7039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 33026989) ^ 16513494 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 33026989) ^ 11008996 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 33026989) ^ 1942764 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 33026989) ^ 1435956 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 33026989) ^ 4692 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_34091807 : Nat.Prime 34091807 := by
  apply lucas_primality 34091807 (5 : ZMod 34091807)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (89, 1), (27361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (89, 1), (27361, 1)] : List FactorBlock).map factorBlockValue).prod) = 34091807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_89
      · exact prime_twentyTwoT_27361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 34091807) ^ 17045903 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 34091807) ^ 4870258 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 34091807) ^ 383054 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 34091807) ^ 1246 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_35140247 : Nat.Prime 35140247 := by
  apply lucas_primality 35140247 (5 : ZMod 35140247)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17570123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17570123, 1)] : List FactorBlock).map factorBlockValue).prod) = 35140247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_17570123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 35140247) ^ 17570123 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 35140247) ^ 2 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_35853943 : Nat.Prime 35853943 := by
  apply lucas_primality 35853943 (3 : ZMod 35853943)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod) = 35853943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_983
      · exact prime_twentyTwoT_6079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853943) ^ 17926971 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 11951314 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 36474 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 5898 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_41182507 : Nat.Prime 41182507 := by
  apply lucas_primality 41182507 (2 : ZMod 41182507)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (254213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (254213, 1)] : List FactorBlock).map factorBlockValue).prod) = 41182507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_254213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41182507) ^ 20591253 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 41182507) ^ 13727502 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 41182507) ^ 162 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_46704187 : Nat.Prime 46704187 := by
  apply lucas_primality 46704187 (3 : ZMod 46704187)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2594677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2594677, 1)] : List FactorBlock).map factorBlockValue).prod) = 46704187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_2594677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 46704187) ^ 23352093 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 46704187) ^ 15568062 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 46704187) ^ 18 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_51234637 : Nat.Prime 51234637 := by
  apply lucas_primality 51234637 (2 : ZMod 51234637)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (647, 1), (6599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (647, 1), (6599, 1)] : List FactorBlock).map factorBlockValue).prod) = 51234637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_647
      · exact prime_twentyTwoT_6599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51234637) ^ 25617318 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 51234637) ^ 17078212 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 51234637) ^ 79188 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 51234637) ^ 7764 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_53504597 : Nat.Prime 53504597 := by
  apply lucas_primality 53504597 (2 : ZMod 53504597)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (118373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (118373, 1)] : List FactorBlock).map factorBlockValue).prod) = 53504597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_113
      · exact prime_twentyTwoT_118373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 53504597) ^ 26752298 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 53504597) ^ 473492 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 53504597) ^ 452 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_55379759 : Nat.Prime 55379759 := by
  apply lucas_primality 55379759 (7 : ZMod 55379759)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (83, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (83, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod) = 55379759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_83
      · exact prime_twentyTwoT_47659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 55379759) ^ 27689879 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 55379759) ^ 7911394 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 55379759) ^ 667226 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 55379759) ^ 1162 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_57440797 : Nat.Prime 57440797 := by
  apply lucas_primality 57440797 (5 : ZMod 57440797)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (683819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (683819, 1)] : List FactorBlock).map factorBlockValue).prod) = 57440797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_683819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 57440797) ^ 28720398 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 57440797) ^ 19146932 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 57440797) ^ 8205828 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 57440797) ^ 84 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_60308257 : Nat.Prime 60308257 := by
  apply lucas_primality 60308257 (5 : ZMod 60308257)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (643, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (643, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) = 60308257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_643
      · exact prime_twentyTwoT_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 60308257) ^ 30154128 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 60308257) ^ 20102752 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 60308257) ^ 93792 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 60308257) ^ 61728 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_61359533 : Nat.Prime 61359533 := by
  apply lucas_primality 61359533 (2 : ZMod 61359533)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (1179991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (1179991, 1)] : List FactorBlock).map factorBlockValue).prod) = 61359533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_1179991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 61359533) ^ 30679766 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 61359533) ^ 4719964 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 61359533) ^ 52 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_68164727 : Nat.Prime 68164727 := by
  apply lucas_primality 68164727 (5 : ZMod 68164727)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4868909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4868909, 1)] : List FactorBlock).map factorBlockValue).prod) = 68164727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_4868909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 68164727) ^ 34082363 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 68164727) ^ 9737818 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 68164727) ^ 14 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_74144261 : Nat.Prime 74144261 := by
  apply lucas_primality 74144261 (2 : ZMod 74144261)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3707213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3707213, 1)] : List FactorBlock).map factorBlockValue).prod) = 74144261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_3707213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 74144261) ^ 37072130 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 74144261) ^ 14828852 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 74144261) ^ 20 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_75111599 : Nat.Prime 75111599 := by
  apply lucas_primality 75111599 (17 : ZMod 75111599)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (73, 1), (27077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (73, 1), (27077, 1)] : List FactorBlock).map factorBlockValue).prod) = 75111599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_73
      · exact prime_twentyTwoT_27077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 75111599) ^ 37555799 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (17 : ZMod 75111599) ^ 3953242 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (17 : ZMod 75111599) ^ 1028926 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (17 : ZMod 75111599) ^ 2774 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_80744533 : Nat.Prime 80744533 := by
  apply lucas_primality 80744533 (6 : ZMod 80744533)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (151, 1), (4051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (151, 1), (4051, 1)] : List FactorBlock).map factorBlockValue).prod) = 80744533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_151
      · exact prime_twentyTwoT_4051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 80744533) ^ 40372266 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 80744533) ^ 26914844 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 80744533) ^ 7340412 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 80744533) ^ 534732 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 80744533) ^ 19932 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_91432559 : Nat.Prime 91432559 := by
  apply lucas_primality 91432559 (7 : ZMod 91432559)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (599, 1), (10903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (599, 1), (10903, 1)] : List FactorBlock).map factorBlockValue).prod) = 91432559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_599
      · exact prime_twentyTwoT_10903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 91432559) ^ 45716279 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 91432559) ^ 13061794 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 91432559) ^ 152642 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 91432559) ^ 8386 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_98695889 : Nat.Prime 98695889 := by
  apply lucas_primality 98695889 (3 : ZMod 98695889)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (967, 1), (6379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (967, 1), (6379, 1)] : List FactorBlock).map factorBlockValue).prod) = 98695889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_967
      · exact prime_twentyTwoT_6379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 98695889) ^ 49347944 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 98695889) ^ 102064 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 98695889) ^ 15472 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_103835981 : Nat.Prime 103835981 := by
  apply lucas_primality 103835981 (2 : ZMod 103835981)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (5191799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (5191799, 1)] : List FactorBlock).map factorBlockValue).prod) = 103835981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_5191799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 103835981) ^ 51917990 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 103835981) ^ 20767196 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 103835981) ^ 20 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_107890579 : Nat.Prime 107890579 := by
  apply lucas_primality 107890579 (3 : ZMod 107890579)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (61, 1), (97, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (61, 1), (97, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) = 107890579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_61
      · exact prime_twentyTwoT_97
      · exact prime_twentyTwoT_1013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 107890579) ^ 53945289 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 107890579) ^ 35963526 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 107890579) ^ 1768698 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 107890579) ^ 1112274 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 107890579) ^ 106506 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_118826887 : Nat.Prime 118826887 := by
  apply lucas_primality 118826887 (6 : ZMod 118826887)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19804481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19804481, 1)] : List FactorBlock).map factorBlockValue).prod) = 118826887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_19804481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 118826887) ^ 59413443 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 118826887) ^ 39608962 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 118826887) ^ 6 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_127435031 : Nat.Prime 127435031 := by
  apply lucas_primality 127435031 (11 : ZMod 127435031)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (163, 1), (2113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (163, 1), (2113, 1)] : List FactorBlock).map factorBlockValue).prod) = 127435031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_37
      · exact prime_twentyTwoT_163
      · exact prime_twentyTwoT_2113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 127435031) ^ 63717515 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 127435031) ^ 25487006 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 127435031) ^ 3444190 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 127435031) ^ 781810 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 127435031) ^ 60310 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_134406001 : Nat.Prime 134406001 := by
  apply lucas_primality 134406001 (17 : ZMod 134406001)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 3), (19, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 3), (19, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) = 134406001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 134406001) ^ 67203000 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (17 : ZMod 134406001) ^ 44802000 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (17 : ZMod 134406001) ^ 26881200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (17 : ZMod 134406001) ^ 7074000 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (17 : ZMod 134406001) ^ 1026000 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_140770891 : Nat.Prime 140770891 := by
  apply lucas_primality 140770891 (2 : ZMod 140770891)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 1), (79, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 1), (79, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) = 140770891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_79
      · exact prime_twentyTwoT_1523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 140770891) ^ 70385445 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 140770891) ^ 46923630 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 140770891) ^ 28154178 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 140770891) ^ 10828530 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 140770891) ^ 1781910 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 140770891) ^ 92430 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_157696507 : Nat.Prime 157696507 := by
  apply lucas_primality 157696507 (2 : ZMod 157696507)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (796447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (796447, 1)] : List FactorBlock).map factorBlockValue).prod) = 157696507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_796447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 157696507) ^ 78848253 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 157696507) ^ 52565502 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 157696507) ^ 14336046 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 157696507) ^ 198 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_161379451 : Nat.Prime 161379451 := by
  apply lucas_primality 161379451 (2 : ZMod 161379451)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (71, 1), (5051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (71, 1), (5051, 1)] : List FactorBlock).map factorBlockValue).prod) = 161379451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_71
      · exact prime_twentyTwoT_5051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161379451) ^ 80689725 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 161379451) ^ 53793150 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 161379451) ^ 32275890 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 161379451) ^ 2272950 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 161379451) ^ 31950 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_165895313 : Nat.Prime 165895313 := by
  apply lucas_primality 165895313 (3 : ZMod 165895313)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (29, 1), (32503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (29, 1), (32503, 1)] : List FactorBlock).map factorBlockValue).prod) = 165895313 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_29
      · exact prime_twentyTwoT_32503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 165895313) ^ 82947656 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 165895313) ^ 15081392 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 165895313) ^ 5720528 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 165895313) ^ 5104 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_180010403 : Nat.Prime 180010403 := by
  apply lucas_primality 180010403 (2 : ZMod 180010403)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (37, 1), (17011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (37, 1), (17011, 1)] : List FactorBlock).map factorBlockValue).prod) = 180010403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_37
      · exact prime_twentyTwoT_17011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 180010403) ^ 90005201 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 180010403) ^ 16364582 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 180010403) ^ 13846954 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 180010403) ^ 4865146 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 180010403) ^ 10582 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_180892039 : Nat.Prime 180892039 := by
  apply lucas_primality 180892039 (3 : ZMod 180892039)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (814829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (814829, 1)] : List FactorBlock).map factorBlockValue).prod) = 180892039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_37
      · exact prime_twentyTwoT_814829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 180892039) ^ 90446019 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 180892039) ^ 60297346 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 180892039) ^ 4888974 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 180892039) ^ 222 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_188131817 : Nat.Prime 188131817 := by
  apply lucas_primality 188131817 (3 : ZMod 188131817)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (810913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (810913, 1)] : List FactorBlock).map factorBlockValue).prod) = 188131817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_29
      · exact prime_twentyTwoT_810913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 188131817) ^ 94065908 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 188131817) ^ 6487304 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 188131817) ^ 232 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_204938549 : Nat.Prime 204938549 := by
  apply lucas_primality 204938549 (2 : ZMod 204938549)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (51234637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (51234637, 1)] : List FactorBlock).map factorBlockValue).prod) = 204938549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_51234637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 204938549) ^ 102469274 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 204938549) ^ 4 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_237044449 : Nat.Prime 237044449 := by
  apply lucas_primality 237044449 (14 : ZMod 237044449)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (274357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (274357, 1)] : List FactorBlock).map factorBlockValue).prod) = 237044449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_274357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 237044449) ^ 118522224 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (14 : ZMod 237044449) ^ 79014816 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (14 : ZMod 237044449) ^ 864 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_191
      · exact prime_twentyTwoT_383
      · exact prime_twentyTwoT_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_251922637 : Nat.Prime 251922637 := by
  apply lucas_primality 251922637 (2 : ZMod 251922637)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (7, 1), (277, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (7, 1), (277, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod) = 251922637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_277
      · exact prime_twentyTwoT_401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 251922637) ^ 125961318 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 251922637) ^ 83974212 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 251922637) ^ 35988948 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 251922637) ^ 909468 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 251922637) ^ 628236 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_263298383 : Nat.Prime 263298383 := by
  apply lucas_primality 263298383 (5 : ZMod 263298383)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (137, 1), (18131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (137, 1), (18131, 1)] : List FactorBlock).map factorBlockValue).prod) = 263298383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_53
      · exact prime_twentyTwoT_137
      · exact prime_twentyTwoT_18131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 263298383) ^ 131649191 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 263298383) ^ 4967894 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 263298383) ^ 1921886 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 263298383) ^ 14522 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_279180007 : Nat.Prime 279180007 := by
  apply lucas_primality 279180007 (3 : ZMod 279180007)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (89, 1), (74687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (89, 1), (74687, 1)] : List FactorBlock).map factorBlockValue).prod) = 279180007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_89
      · exact prime_twentyTwoT_74687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 279180007) ^ 139590003 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 279180007) ^ 93060002 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 279180007) ^ 39882858 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 279180007) ^ 3136854 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 279180007) ^ 3738 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_282104549 : Nat.Prime 282104549 := by
  apply lucas_primality 282104549 (2 : ZMod 282104549)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (6411467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (6411467, 1)] : List FactorBlock).map factorBlockValue).prod) = 282104549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_6411467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 282104549) ^ 141052274 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 282104549) ^ 25645868 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 282104549) ^ 44 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_289278289 : Nat.Prime 289278289 := by
  apply lucas_primality 289278289 (7 : ZMod 289278289)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (13, 1), (41, 1), (3769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (13, 1), (41, 1), (3769, 1)] : List FactorBlock).map factorBlockValue).prod) = 289278289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_41
      · exact prime_twentyTwoT_3769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 289278289) ^ 144639144 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 289278289) ^ 96426096 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 289278289) ^ 22252176 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 289278289) ^ 7055568 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 289278289) ^ 76752 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_294725971 : Nat.Prime 294725971 := by
  apply lucas_primality 294725971 (11 : ZMod 294725971)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (71, 1), (599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (71, 1), (599, 1)] : List FactorBlock).map factorBlockValue).prod) = 294725971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_71
      · exact prime_twentyTwoT_599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 294725971) ^ 147362985 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 294725971) ^ 98241990 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 294725971) ^ 58945194 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 294725971) ^ 42103710 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 294725971) ^ 26793270 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 294725971) ^ 4151070 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 294725971) ^ 492030 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_313629971 : Nat.Prime 313629971 := by
  apply lucas_primality 313629971 (2 : ZMod 313629971)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (173, 1), (199, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (173, 1), (199, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) = 313629971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_173
      · exact prime_twentyTwoT_199
      · exact prime_twentyTwoT_911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 313629971) ^ 156814985 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 313629971) ^ 62725994 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 313629971) ^ 1812890 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 313629971) ^ 1576030 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 313629971) ^ 344270 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_330443381 : Nat.Prime 330443381 := by
  apply lucas_primality 330443381 (2 : ZMod 330443381)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (163, 1), (101363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (163, 1), (101363, 1)] : List FactorBlock).map factorBlockValue).prod) = 330443381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_163
      · exact prime_twentyTwoT_101363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 330443381) ^ 165221690 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 330443381) ^ 66088676 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 330443381) ^ 2027260 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 330443381) ^ 3260 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_369688933 : Nat.Prime 369688933 := by
  apply lucas_primality 369688933 (5 : ZMod 369688933)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (10269137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (10269137, 1)] : List FactorBlock).map factorBlockValue).prod) = 369688933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_10269137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 369688933) ^ 184844466 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 369688933) ^ 123229644 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 369688933) ^ 36 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_423992911 : Nat.Prime 423992911 := by
  apply lucas_primality 423992911 (11 : ZMod 423992911)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (149, 1), (8623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (149, 1), (8623, 1)] : List FactorBlock).map factorBlockValue).prod) = 423992911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_149
      · exact prime_twentyTwoT_8623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 423992911) ^ 211996455 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 423992911) ^ 141330970 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 423992911) ^ 84798582 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 423992911) ^ 38544810 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 423992911) ^ 2845590 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 423992911) ^ 49170 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_435015923 : Nat.Prime 435015923 := by
  apply lucas_primality 435015923 (2 : ZMod 435015923)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19773451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19773451, 1)] : List FactorBlock).map factorBlockValue).prod) = 435015923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_19773451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 435015923) ^ 217507961 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 435015923) ^ 39546902 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 435015923) ^ 22 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_451071857 : Nat.Prime 451071857 := by
  apply lucas_primality 451071857 (3 : ZMod 451071857)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (163, 1), (9103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (163, 1), (9103, 1)] : List FactorBlock).map factorBlockValue).prod) = 451071857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_163
      · exact prime_twentyTwoT_9103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 451071857) ^ 225535928 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 451071857) ^ 23740624 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 451071857) ^ 2767312 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 451071857) ^ 49552 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_465392159 : Nat.Prime 465392159 := by
  apply lucas_primality 465392159 (7 : ZMod 465392159)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (3022027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (3022027, 1)] : List FactorBlock).map factorBlockValue).prod) = 465392159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_3022027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 465392159) ^ 232696079 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 465392159) ^ 66484594 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 465392159) ^ 42308378 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 465392159) ^ 154 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_533624659 : Nat.Prime 533624659 := by
  apply lucas_primality 533624659 (7 : ZMod 533624659)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (12705349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (12705349, 1)] : List FactorBlock).map factorBlockValue).prod) = 533624659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_12705349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 533624659) ^ 266812329 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 533624659) ^ 177874886 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 533624659) ^ 76232094 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 533624659) ^ 42 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_566707819 : Nat.Prime 566707819 := by
  apply lucas_primality 566707819 (3 : ZMod 566707819)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (1709, 1), (3251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (1709, 1), (3251, 1)] : List FactorBlock).map factorBlockValue).prod) = 566707819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_17
      · exact prime_twentyTwoT_1709
      · exact prime_twentyTwoT_3251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 566707819) ^ 283353909 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 566707819) ^ 188902606 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 566707819) ^ 33335754 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 566707819) ^ 331602 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 566707819) ^ 174318 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_628384961 : Nat.Prime 628384961 := by
  apply lucas_primality 628384961 (6 : ZMod 628384961)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (7, 1), (53, 1), (67, 1), (79, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (7, 1), (53, 1), (67, 1), (79, 1)] : List FactorBlock).map factorBlockValue).prod) = 628384961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_53
      · exact prime_twentyTwoT_67
      · exact prime_twentyTwoT_79
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 628384961) ^ 314192480 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 628384961) ^ 125676992 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 628384961) ^ 89769280 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 628384961) ^ 11856320 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 628384961) ^ 9378880 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 628384961) ^ 7954240 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_767926501 : Nat.Prime 767926501 := by
  apply lucas_primality 767926501 (2 : ZMod 767926501)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (11, 2), (4231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (11, 2), (4231, 1)] : List FactorBlock).map factorBlockValue).prod) = 767926501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_4231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 767926501) ^ 383963250 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 767926501) ^ 255975500 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 767926501) ^ 153585300 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 767926501) ^ 69811500 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 767926501) ^ 181500 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_889731133 : Nat.Prime 889731133 := by
  apply lucas_primality 889731133 (2 : ZMod 889731133)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (74144261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (74144261, 1)] : List FactorBlock).map factorBlockValue).prod) = 889731133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_74144261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 889731133) ^ 444865566 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 889731133) ^ 296577044 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 889731133) ^ 12 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_930509509 : Nat.Prime 930509509 := by
  apply lucas_primality 930509509 (6 : ZMod 930509509)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (593, 1), (3041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (593, 1), (3041, 1)] : List FactorBlock).map factorBlockValue).prod) = 930509509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_43
      · exact prime_twentyTwoT_593
      · exact prime_twentyTwoT_3041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 930509509) ^ 465254754 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 930509509) ^ 310169836 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 930509509) ^ 21639756 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 930509509) ^ 1569156 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 930509509) ^ 305988 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_946695979 : Nat.Prime 946695979 := by
  apply lucas_primality 946695979 (2 : ZMod 946695979)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (2351, 1), (7457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (2351, 1), (7457, 1)] : List FactorBlock).map factorBlockValue).prod) = 946695979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_2351
      · exact prime_twentyTwoT_7457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 946695979) ^ 473347989 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 946695979) ^ 315565326 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 946695979) ^ 402678 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 946695979) ^ 126954 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_963143029 : Nat.Prime 963143029 := by
  apply lucas_primality 963143029 (2 : ZMod 963143029)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (8917991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (8917991, 1)] : List FactorBlock).map factorBlockValue).prod) = 963143029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_8917991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 963143029) ^ 481571514 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 963143029) ^ 321047676 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 963143029) ^ 108 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1073490031 : Nat.Prime 1073490031 := by
  apply lucas_primality 1073490031 (3 : ZMod 1073490031)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (409, 1), (9721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (409, 1), (9721, 1)] : List FactorBlock).map factorBlockValue).prod) = 1073490031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_409
      · exact prime_twentyTwoT_9721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1073490031) ^ 536745015 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1073490031) ^ 357830010 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1073490031) ^ 214698006 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1073490031) ^ 2624670 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1073490031) ^ 110430 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1138844891 : Nat.Prime 1138844891 := by
  apply lucas_primality 1138844891 (2 : ZMod 1138844891)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (89, 1), (1279601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (89, 1), (1279601, 1)] : List FactorBlock).map factorBlockValue).prod) = 1138844891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_89
      · exact prime_twentyTwoT_1279601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1138844891) ^ 569422445 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1138844891) ^ 227768978 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1138844891) ^ 12796010 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1138844891) ^ 890 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_29
      · exact prime_twentyTwoT_113
      · exact prime_twentyTwoT_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1256579221 : Nat.Prime 1256579221 := by
  apply lucas_primality 1256579221 (6 : ZMod 1256579221)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 2), (123923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 2), (123923, 1)] : List FactorBlock).map factorBlockValue).prod) = 1256579221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_123923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1256579221) ^ 628289610 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1256579221) ^ 418859740 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1256579221) ^ 251315844 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1256579221) ^ 96659940 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1256579221) ^ 10140 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1304698691 : Nat.Prime 1304698691 := by
  apply lucas_primality 1304698691 (6 : ZMod 1304698691)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (29, 1), (43, 1), (4549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (29, 1), (43, 1), (4549, 1)] : List FactorBlock).map factorBlockValue).prod) = 1304698691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_23
      · exact prime_twentyTwoT_29
      · exact prime_twentyTwoT_43
      · exact prime_twentyTwoT_4549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1304698691) ^ 652349345 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1304698691) ^ 260939738 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1304698691) ^ 56726030 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1304698691) ^ 44989610 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1304698691) ^ 30341830 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1304698691) ^ 286810 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1543503319 : Nat.Prime 1543503319 := by
  apply lucas_primality 1543503319 (3 : ZMod 1543503319)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (43, 1), (757, 1), (1129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (43, 1), (757, 1), (1129, 1)] : List FactorBlock).map factorBlockValue).prod) = 1543503319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_43
      · exact prime_twentyTwoT_757
      · exact prime_twentyTwoT_1129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1543503319) ^ 771751659 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1543503319) ^ 514501106 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1543503319) ^ 220500474 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1543503319) ^ 35895426 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1543503319) ^ 2038974 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1543503319) ^ 1367142 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1596258817 : Nat.Prime 1596258817 := by
  apply lucas_primality 1596258817 (5 : ZMod 1596258817)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (191, 1), (5441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (191, 1), (5441, 1)] : List FactorBlock).map factorBlockValue).prod) = 1596258817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_191
      · exact prime_twentyTwoT_5441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1596258817) ^ 798129408 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1596258817) ^ 532086272 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1596258817) ^ 8357376 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1596258817) ^ 293376 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1773847591 : Nat.Prime 1773847591 := by
  apply lucas_primality 1773847591 (3 : ZMod 1773847591)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (311, 1), (6133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (311, 1), (6133, 1)] : List FactorBlock).map factorBlockValue).prod) = 1773847591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_31
      · exact prime_twentyTwoT_311
      · exact prime_twentyTwoT_6133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1773847591) ^ 886923795 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1773847591) ^ 591282530 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1773847591) ^ 354769518 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1773847591) ^ 57220890 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1773847591) ^ 5703690 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1773847591) ^ 289230 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1904284259 : Nat.Prime 1904284259 := by
  apply lucas_primality 1904284259 (2 : ZMod 1904284259)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29873, 1), (31873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29873, 1), (31873, 1)] : List FactorBlock).map factorBlockValue).prod) = 1904284259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_29873
      · exact prime_twentyTwoT_31873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1904284259) ^ 952142129 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1904284259) ^ 63746 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1904284259) ^ 59746 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2064319931 : Nat.Prime 2064319931 := by
  apply lucas_primality 2064319931 (2 : ZMod 2064319931)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (401, 1), (514793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (401, 1), (514793, 1)] : List FactorBlock).map factorBlockValue).prod) = 2064319931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_401
      · exact prime_twentyTwoT_514793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2064319931) ^ 1032159965 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2064319931) ^ 412863986 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2064319931) ^ 5147930 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2064319931) ^ 4010 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2170704469 : Nat.Prime 2170704469 := by
  apply lucas_primality 2170704469 (6 : ZMod 2170704469)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (180892039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (180892039, 1)] : List FactorBlock).map factorBlockValue).prod) = 2170704469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_180892039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 2170704469) ^ 1085352234 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2170704469) ^ 723568156 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2170704469) ^ 12 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2278167139 : Nat.Prime 2278167139 := by
  apply lucas_primality 2278167139 (2 : ZMod 2278167139)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (1553, 1), (6269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (1553, 1), (6269, 1)] : List FactorBlock).map factorBlockValue).prod) = 2278167139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_1553
      · exact prime_twentyTwoT_6269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2278167139) ^ 1139083569 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2278167139) ^ 759389046 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2278167139) ^ 175243626 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2278167139) ^ 1466946 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2278167139) ^ 363402 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2285686021 : Nat.Prime 2285686021 := by
  apply lucas_primality 2285686021 (6 : ZMod 2285686021)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (3221, 1), (11827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (3221, 1), (11827, 1)] : List FactorBlock).map factorBlockValue).prod) = 2285686021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_3221
      · exact prime_twentyTwoT_11827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2285686021) ^ 1142843010 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2285686021) ^ 761895340 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2285686021) ^ 457137204 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2285686021) ^ 709620 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2285686021) ^ 193260 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2370444491 : Nat.Prime 2370444491 := by
  apply lucas_primality 2370444491 (2 : ZMod 2370444491)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (237044449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (237044449, 1)] : List FactorBlock).map factorBlockValue).prod) = 2370444491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_237044449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2370444491) ^ 1185222245 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2370444491) ^ 474088898 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2370444491) ^ 10 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2533876039 : Nat.Prime 2533876039 := by
  apply lucas_primality 2533876039 (6 : ZMod 2533876039)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (140770891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (140770891, 1)] : List FactorBlock).map factorBlockValue).prod) = 2533876039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_140770891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 2533876039) ^ 1266938019 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2533876039) ^ 844625346 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2533876039) ^ 18 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2671091477 : Nat.Prime 2671091477 := by
  apply lucas_primality 2671091477 (2 : ZMod 2671091477)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (23, 1), (401, 1), (4259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (23, 1), (401, 1), (4259, 1)] : List FactorBlock).map factorBlockValue).prod) = 2671091477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_17
      · exact prime_twentyTwoT_23
      · exact prime_twentyTwoT_401
      · exact prime_twentyTwoT_4259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2671091477) ^ 1335545738 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2671091477) ^ 157123028 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2671091477) ^ 116134412 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2671091477) ^ 6661076 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2671091477) ^ 627164 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2692104817 : Nat.Prime 2692104817 := by
  apply lucas_primality 2692104817 (5 : ZMod 2692104817)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (653, 1), (85889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (653, 1), (85889, 1)] : List FactorBlock).map factorBlockValue).prod) = 2692104817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_653
      · exact prime_twentyTwoT_85889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2692104817) ^ 1346052408 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2692104817) ^ 897368272 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2692104817) ^ 4122672 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2692104817) ^ 31344 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2779889117 : Nat.Prime 2779889117 := by
  apply lucas_primality 2779889117 (2 : ZMod 2779889117)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19553, 1), (35543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19553, 1), (35543, 1)] : List FactorBlock).map factorBlockValue).prod) = 2779889117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_19553
      · exact prime_twentyTwoT_35543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2779889117) ^ 1389944558 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2779889117) ^ 142172 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2779889117) ^ 78212 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2848589311 : Nat.Prime 2848589311 := by
  apply lucas_primality 2848589311 (6 : ZMod 2848589311)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (107, 1), (331, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (107, 1), (331, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) = 2848589311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_107
      · exact prime_twentyTwoT_331
      · exact prime_twentyTwoT_383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2848589311) ^ 1424294655 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 949529770 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 569717862 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 406941330 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 26622330 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 8606010 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 7437570 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2871090773 : Nat.Prime 2871090773 := by
  apply lucas_primality 2871090773 (2 : ZMod 2871090773)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (53, 1), (1231171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (53, 1), (1231171, 1)] : List FactorBlock).map factorBlockValue).prod) = 2871090773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_53
      · exact prime_twentyTwoT_1231171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2871090773) ^ 1435545386 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871090773) ^ 261008252 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871090773) ^ 54171524 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871090773) ^ 2332 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_3866391601 : Nat.Prime 3866391601 := by
  apply lucas_primality 3866391601 (13 : ZMod 3866391601)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (17, 1), (189529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (17, 1), (189529, 1)] : List FactorBlock).map factorBlockValue).prod) = 3866391601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_17
      · exact prime_twentyTwoT_189529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3866391601) ^ 1933195800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 3866391601) ^ 1288797200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 3866391601) ^ 773278320 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 3866391601) ^ 227434800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 3866391601) ^ 20400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_4049080921 : Nat.Prime 4049080921 := by
  apply lucas_primality 4049080921 (11 : ZMod 4049080921)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (29, 1), (129281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (29, 1), (129281, 1)] : List FactorBlock).map factorBlockValue).prod) = 4049080921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_29
      · exact prime_twentyTwoT_129281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4049080921) ^ 2024540460 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 4049080921) ^ 1349693640 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 4049080921) ^ 809816184 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 4049080921) ^ 139623480 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 4049080921) ^ 31320 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_4223193659 : Nat.Prime 4223193659 := by
  apply lucas_primality 4223193659 (2 : ZMod 4223193659)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 2), (1142021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 2), (1142021, 1)] : List FactorBlock).map factorBlockValue).prod) = 4223193659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_43
      · exact prime_twentyTwoT_1142021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4223193659) ^ 2111596829 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4223193659) ^ 98213806 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4223193659) ^ 3698 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_4465368571 : Nat.Prime 4465368571 := by
  apply lucas_primality 4465368571 (2 : ZMod 4465368571)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (101, 1), (113363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (101, 1), (113363, 1)] : List FactorBlock).map factorBlockValue).prod) = 4465368571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_101
      · exact prime_twentyTwoT_113363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4465368571) ^ 2232684285 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4465368571) ^ 1488456190 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4465368571) ^ 893073714 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4465368571) ^ 343489890 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4465368571) ^ 44211570 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4465368571) ^ 39390 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_4914710321 : Nat.Prime 4914710321 := by
  apply lucas_primality 4914710321 (3 : ZMod 4914710321)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (13, 1), (4725683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (13, 1), (4725683, 1)] : List FactorBlock).map factorBlockValue).prod) = 4914710321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_4725683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4914710321) ^ 2457355160 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914710321) ^ 982942064 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914710321) ^ 378054640 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914710321) ^ 1040 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_4977157963 : Nat.Prime 4977157963 := by
  apply lucas_primality 4977157963 (7 : ZMod 4977157963)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (223, 1), (227, 1), (2341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (223, 1), (227, 1), (2341, 1)] : List FactorBlock).map factorBlockValue).prod) = 4977157963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_223
      · exact prime_twentyTwoT_227
      · exact prime_twentyTwoT_2341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4977157963) ^ 2488578981 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 4977157963) ^ 1659052654 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 4977157963) ^ 711022566 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 4977157963) ^ 22319094 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 4977157963) ^ 21925806 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 4977157963) ^ 2126082 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_5118840821 : Nat.Prime 5118840821 := by
  apply lucas_primality 5118840821 (2 : ZMod 5118840821)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1291, 1), (198251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1291, 1), (198251, 1)] : List FactorBlock).map factorBlockValue).prod) = 5118840821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_1291
      · exact prime_twentyTwoT_198251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5118840821) ^ 2559420410 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5118840821) ^ 1023768164 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5118840821) ^ 3965020 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5118840821) ^ 25820 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_5353725911 : Nat.Prime 5353725911 := by
  apply lucas_primality 5353725911 (7 : ZMod 5353725911)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (41182507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (41182507, 1)] : List FactorBlock).map factorBlockValue).prod) = 5353725911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_41182507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 5353725911) ^ 2676862955 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 5353725911) ^ 1070745182 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 5353725911) ^ 411825070 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 5353725911) ^ 130 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_5789592673 : Nat.Prime 5789592673 := by
  apply lucas_primality 5789592673 (10 : ZMod 5789592673)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (60308257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (60308257, 1)] : List FactorBlock).map factorBlockValue).prod) = 5789592673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_60308257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 5789592673) ^ 2894796336 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (10 : ZMod 5789592673) ^ 1929864224 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (10 : ZMod 5789592673) ^ 96 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_6385035269 : Nat.Prime 6385035269 := by
  apply lucas_primality 6385035269 (2 : ZMod 6385035269)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1596258817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1596258817, 1)] : List FactorBlock).map factorBlockValue).prod) = 6385035269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_1596258817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 6385035269) ^ 3192517634 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6385035269) ^ 4 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_7088013991 : Nat.Prime 7088013991 := by
  apply lucas_primality 7088013991 (11 : ZMod 7088013991)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (41, 1), (151, 1), (12721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (41, 1), (151, 1), (12721, 1)] : List FactorBlock).map factorBlockValue).prod) = 7088013991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_41
      · exact prime_twentyTwoT_151
      · exact prime_twentyTwoT_12721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 7088013991) ^ 3544006995 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 2362671330 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 1417602798 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 172878390 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 46940490 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 557190 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_7948202681 : Nat.Prime 7948202681 := by
  apply lucas_primality 7948202681 (3 : ZMod 7948202681)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (2339, 1), (7723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (2339, 1), (7723, 1)] : List FactorBlock).map factorBlockValue).prod) = 7948202681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_2339
      · exact prime_twentyTwoT_7723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7948202681) ^ 3974101340 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 7948202681) ^ 1589640536 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 7948202681) ^ 722563880 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 7948202681) ^ 3398120 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 7948202681) ^ 1029160 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_10707451823 : Nat.Prime 10707451823 := by
  apply lucas_primality 10707451823 (5 : ZMod 10707451823)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5353725911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5353725911, 1)] : List FactorBlock).map factorBlockValue).prod) = 10707451823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5353725911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 10707451823) ^ 5353725911 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 10707451823) ^ 2 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_10770026867 : Nat.Prime 10770026867 := by
  apply lucas_primality 10770026867 (2 : ZMod 10770026867)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (68164727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (68164727, 1)] : List FactorBlock).map factorBlockValue).prod) = 10770026867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_79
      · exact prime_twentyTwoT_68164727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10770026867) ^ 5385013433 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10770026867) ^ 136329454 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10770026867) ^ 158 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_11339536811 : Nat.Prime 11339536811 := by
  apply lucas_primality 11339536811 (6 : ZMod 11339536811)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (5225593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (5225593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11339536811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_31
      · exact prime_twentyTwoT_5225593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 11339536811) ^ 5669768405 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 11339536811) ^ 2267907362 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 11339536811) ^ 1619933830 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 11339536811) ^ 365791510 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 11339536811) ^ 2170 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_15837208853 : Nat.Prime 15837208853 := by
  apply lucas_primality 15837208853 (2 : ZMod 15837208853)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (9257, 1), (22511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (9257, 1), (22511, 1)] : List FactorBlock).map factorBlockValue).prod) = 15837208853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_9257
      · exact prime_twentyTwoT_22511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15837208853) ^ 7918604426 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 15837208853) ^ 833537308 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 15837208853) ^ 1710836 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 15837208853) ^ 703532 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_18299340599 : Nat.Prime 18299340599 := by
  apply lucas_primality 18299340599 (7 : ZMod 18299340599)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (118826887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (118826887, 1)] : List FactorBlock).map factorBlockValue).prod) = 18299340599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_118826887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 18299340599) ^ 9149670299 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 18299340599) ^ 2614191514 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 18299340599) ^ 1663576418 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 18299340599) ^ 154 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_18918168251 : Nat.Prime 18918168251 := by
  apply lucas_primality 18918168251 (2 : ZMod 18918168251)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (7867, 1), (9619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (7867, 1), (9619, 1)] : List FactorBlock).map factorBlockValue).prod) = 18918168251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_7867
      · exact prime_twentyTwoT_9619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18918168251) ^ 9459084125 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 18918168251) ^ 3783633650 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 18918168251) ^ 2404750 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 18918168251) ^ 1966750 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_19748623057 : Nat.Prime 19748623057 := by
  apply lucas_primality 19748623057 (10 : ZMod 19748623057)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (67, 1), (157, 1), (39113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (67, 1), (157, 1), (39113, 1)] : List FactorBlock).map factorBlockValue).prod) = 19748623057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_67
      · exact prime_twentyTwoT_157
      · exact prime_twentyTwoT_39113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 19748623057) ^ 9874311528 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (10 : ZMod 19748623057) ^ 6582874352 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (10 : ZMod 19748623057) ^ 294755568 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (10 : ZMod 19748623057) ^ 125787408 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (10 : ZMod 19748623057) ^ 504912 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_21846394897 : Nat.Prime 21846394897 := by
  apply lucas_primality 21846394897 (5 : ZMod 21846394897)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (31, 1), (14681717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (31, 1), (14681717, 1)] : List FactorBlock).map factorBlockValue).prod) = 21846394897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_31
      · exact prime_twentyTwoT_14681717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 21846394897) ^ 10923197448 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 21846394897) ^ 7282131632 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 21846394897) ^ 704722416 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 21846394897) ^ 1488 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_21995500987 : Nat.Prime 21995500987 := by
  apply lucas_primality 21995500987 (3 : ZMod 21995500987)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5417, 1), (225581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5417, 1), (225581, 1)] : List FactorBlock).map factorBlockValue).prod) = 21995500987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5417
      · exact prime_twentyTwoT_225581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 21995500987) ^ 10997750493 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 21995500987) ^ 7331833662 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 21995500987) ^ 4060458 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 21995500987) ^ 97506 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_28920407891 : Nat.Prime 28920407891 := by
  apply lucas_primality 28920407891 (2 : ZMod 28920407891)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (257, 1), (269, 1), (3803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (257, 1), (269, 1), (3803, 1)] : List FactorBlock).map factorBlockValue).prod) = 28920407891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_257
      · exact prime_twentyTwoT_269
      · exact prime_twentyTwoT_3803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28920407891) ^ 14460203945 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28920407891) ^ 5784081578 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28920407891) ^ 2629127990 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28920407891) ^ 112530770 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28920407891) ^ 107510810 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28920407891) ^ 7604630 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_29304298123 : Nat.Prime 29304298123 := by
  apply lucas_primality 29304298123 (2 : ZMod 29304298123)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (1229, 1), (32843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (1229, 1), (32843, 1)] : List FactorBlock).map factorBlockValue).prod) = 29304298123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_1229
      · exact prime_twentyTwoT_32843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29304298123) ^ 14652149061 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 29304298123) ^ 9768099374 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 29304298123) ^ 2664027102 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 29304298123) ^ 23844018 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 29304298123) ^ 892254 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_36598681199 : Nat.Prime 36598681199 := by
  apply lucas_primality 36598681199 (11 : ZMod 36598681199)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18299340599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18299340599, 1)] : List FactorBlock).map factorBlockValue).prod) = 36598681199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_18299340599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 36598681199) ^ 18299340599 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 36598681199) ^ 2 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_36966987433 : Nat.Prime 36966987433 := by
  apply lucas_primality 36966987433 (5 : ZMod 36966987433)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (353, 1), (1454477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (353, 1), (1454477, 1)] : List FactorBlock).map factorBlockValue).prod) = 36966987433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_353
      · exact prime_twentyTwoT_1454477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 36966987433) ^ 18483493716 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 36966987433) ^ 12322329144 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 36966987433) ^ 104722344 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 36966987433) ^ 25416 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_151
      · exact prime_twentyTwoT_479
      · exact prime_twentyTwoT_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_45595501013 : Nat.Prime 45595501013 := by
  apply lucas_primality 45595501013 (2 : ZMod 45595501013)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (137, 1), (263, 1), (316363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (137, 1), (263, 1), (316363, 1)] : List FactorBlock).map factorBlockValue).prod) = 45595501013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_137
      · exact prime_twentyTwoT_263
      · exact prime_twentyTwoT_316363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45595501013) ^ 22797750506 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 45595501013) ^ 332813876 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 45595501013) ^ 173366924 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 45595501013) ^ 144124 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_49509601663 : Nat.Prime 49509601663 := by
  apply lucas_primality 49509601663 (5 : ZMod 49509601663)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1801, 1), (4581677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1801, 1), (4581677, 1)] : List FactorBlock).map factorBlockValue).prod) = 49509601663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_1801
      · exact prime_twentyTwoT_4581677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 49509601663) ^ 24754800831 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 49509601663) ^ 16503200554 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 49509601663) ^ 27490062 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 49509601663) ^ 10806 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_54819625657 : Nat.Prime 54819625657 := by
  apply lucas_primality 54819625657 (7 : ZMod 54819625657)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (67, 1), (34091807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (67, 1), (34091807, 1)] : List FactorBlock).map factorBlockValue).prod) = 54819625657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_67
      · exact prime_twentyTwoT_34091807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 54819625657) ^ 27409812828 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 54819625657) ^ 18273208552 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 54819625657) ^ 818203368 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 54819625657) ^ 1608 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_56990814479 : Nat.Prime 56990814479 := by
  apply lucas_primality 56990814479 (7 : ZMod 56990814479)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (827, 1), (1039, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (827, 1), (1039, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) = 56990814479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_827
      · exact prime_twentyTwoT_1039
      · exact prime_twentyTwoT_2551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 56990814479) ^ 28495407239 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 56990814479) ^ 4383908806 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 56990814479) ^ 68912714 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 56990814479) ^ 54851602 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 56990814479) ^ 22340578 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_59254815407 : Nat.Prime 59254815407 := by
  apply lucas_primality 59254815407 (5 : ZMod 59254815407)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (3343, 1), (385327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (3343, 1), (385327, 1)] : List FactorBlock).map factorBlockValue).prod) = 59254815407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_23
      · exact prime_twentyTwoT_3343
      · exact prime_twentyTwoT_385327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 59254815407) ^ 29627407703 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 59254815407) ^ 2576296322 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 59254815407) ^ 17725042 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 59254815407) ^ 153778 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_65252388451 : Nat.Prime 65252388451 := by
  apply lucas_primality 65252388451 (2 : ZMod 65252388451)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (435015923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (435015923, 1)] : List FactorBlock).map factorBlockValue).prod) = 65252388451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_435015923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 65252388451) ^ 32626194225 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 65252388451) ^ 21750796150 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 65252388451) ^ 13050477690 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 65252388451) ^ 150 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_65640100049 : Nat.Prime 65640100049 := by
  apply lucas_primality 65640100049 (3 : ZMod 65640100049)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1663, 1), (2466931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1663, 1), (2466931, 1)] : List FactorBlock).map factorBlockValue).prod) = 65640100049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_1663
      · exact prime_twentyTwoT_2466931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 65640100049) ^ 32820050024 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 65640100049) ^ 39470896 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 65640100049) ^ 26608 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_67971064771 : Nat.Prime 67971064771 := by
  apply lucas_primality 67971064771 (2 : ZMod 67971064771)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (107890579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (107890579, 1)] : List FactorBlock).map factorBlockValue).prod) = 67971064771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_107890579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 67971064771) ^ 33985532385 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 67971064771) ^ 22657021590 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 67971064771) ^ 13594212954 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 67971064771) ^ 9710152110 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 67971064771) ^ 630 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_71487738337 : Nat.Prime 71487738337 := by
  apply lucas_primality 71487738337 (13 : ZMod 71487738337)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (19, 2), (103, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (19, 2), (103, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod) = 71487738337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_103
      · exact prime_twentyTwoT_2861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 71487738337) ^ 35743869168 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 71487738337) ^ 23829246112 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 71487738337) ^ 10212534048 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 71487738337) ^ 3762512544 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 71487738337) ^ 694055712 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 71487738337) ^ 24986976 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_84756586553 : Nat.Prime 84756586553 := by
  apply lucas_primality 84756586553 (3 : ZMod 84756586553)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (963143029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (963143029, 1)] : List FactorBlock).map factorBlockValue).prod) = 84756586553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_963143029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 84756586553) ^ 42378293276 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 84756586553) ^ 7705144232 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 84756586553) ^ 88 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_103039496123 : Nat.Prime 103039496123 := by
  apply lucas_primality 103039496123 (2 : ZMod 103039496123)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (1256579221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (1256579221, 1)] : List FactorBlock).map factorBlockValue).prod) = 103039496123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_41
      · exact prime_twentyTwoT_1256579221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 103039496123) ^ 51519748061 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 103039496123) ^ 2513158442 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 103039496123) ^ 82 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_131280200099 : Nat.Prime 131280200099 := by
  apply lucas_primality 131280200099 (2 : ZMod 131280200099)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (65640100049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (65640100049, 1)] : List FactorBlock).map factorBlockValue).prod) = 131280200099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_65640100049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 131280200099) ^ 65640100049 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 131280200099) ^ 2 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_138448735921 : Nat.Prime 138448735921 := by
  apply lucas_primality 138448735921 (14 : ZMod 138448735921)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 1), (11, 1), (5826967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 1), (11, 1), (5826967, 1)] : List FactorBlock).map factorBlockValue).prod) = 138448735921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_5826967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 138448735921) ^ 69224367960 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 46149578640 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 27689747184 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 12586248720 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 23760 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_141929920049 : Nat.Prime 141929920049 := by
  apply lucas_primality 141929920049 (3 : ZMod 141929920049)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (19, 1), (1753, 1), (38047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (19, 1), (1753, 1), (38047, 1)] : List FactorBlock).map factorBlockValue).prod) = 141929920049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_1753
      · exact prime_twentyTwoT_38047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 141929920049) ^ 70964960024 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 141929920049) ^ 20275702864 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 141929920049) ^ 7469995792 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 141929920049) ^ 80964016 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 141929920049) ^ 3730384 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_151858876903 : Nat.Prime 151858876903 := by
  apply lucas_primality 151858876903 (3 : ZMod 151858876903)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3793, 1), (6672769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3793, 1), (6672769, 1)] : List FactorBlock).map factorBlockValue).prod) = 151858876903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_3793
      · exact prime_twentyTwoT_6672769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 151858876903) ^ 75929438451 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 151858876903) ^ 50619625634 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 151858876903) ^ 40036614 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 151858876903) ^ 22758 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_190507613573 : Nat.Prime 190507613573 := by
  apply lucas_primality 190507613573 (2 : ZMod 190507613573)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (727, 1), (3691, 1), (17749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (727, 1), (3691, 1), (17749, 1)] : List FactorBlock).map factorBlockValue).prod) = 190507613573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_727
      · exact prime_twentyTwoT_3691
      · exact prime_twentyTwoT_17749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 190507613573) ^ 95253806786 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 190507613573) ^ 262046236 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 190507613573) ^ 51614092 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 190507613573) ^ 10733428 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_224916175177 : Nat.Prime 224916175177 := by
  apply lucas_primality 224916175177 (15 : ZMod 224916175177)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (11, 1), (337, 1), (51593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (11, 1), (337, 1), (51593, 1)] : List FactorBlock).map factorBlockValue).prod) = 224916175177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_337
      · exact prime_twentyTwoT_51593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 224916175177) ^ 112458087588 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (15 : ZMod 224916175177) ^ 74972058392 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (15 : ZMod 224916175177) ^ 32130882168 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (15 : ZMod 224916175177) ^ 20446925016 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (15 : ZMod 224916175177) ^ 667407048 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (15 : ZMod 224916175177) ^ 4359432 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_252321361381 : Nat.Prime 252321361381 := by
  apply lucas_primality 252321361381 (2 : ZMod 252321361381)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (11, 1), (127435031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (11, 1), (127435031, 1)] : List FactorBlock).map factorBlockValue).prod) = 252321361381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_127435031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 252321361381) ^ 126160680690 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 252321361381) ^ 84107120460 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 252321361381) ^ 50464272276 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 252321361381) ^ 22938305580 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 252321361381) ^ 1980 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_260519272661 : Nat.Prime 260519272661 := by
  apply lucas_primality 260519272661 (3 : ZMod 260519272661)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (25439, 1), (512047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (25439, 1), (512047, 1)] : List FactorBlock).map factorBlockValue).prod) = 260519272661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_25439
      · exact prime_twentyTwoT_512047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 260519272661) ^ 130259636330 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 260519272661) ^ 52103854532 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 260519272661) ^ 10240940 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 260519272661) ^ 508780 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_331660790141 : Nat.Prime 331660790141 := by
  apply lucas_primality 331660790141 (2 : ZMod 331660790141)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (11933, 1), (73141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (11933, 1), (73141, 1)] : List FactorBlock).map factorBlockValue).prod) = 331660790141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_11933
      · exact prime_twentyTwoT_73141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 331660790141) ^ 165830395070 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 331660790141) ^ 66332158028 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 331660790141) ^ 17455831060 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 331660790141) ^ 27793580 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 331660790141) ^ 4534540 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_358109545763 : Nat.Prime 358109545763 := by
  apply lucas_primality 358109545763 (2 : ZMod 358109545763)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (7013, 1), (432743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (7013, 1), (432743, 1)] : List FactorBlock).map factorBlockValue).prod) = 358109545763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_59
      · exact prime_twentyTwoT_7013
      · exact prime_twentyTwoT_432743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 358109545763) ^ 179054772881 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 358109545763) ^ 6069653318 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 358109545763) ^ 51063674 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 358109545763) ^ 827534 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_362865177953 : Nat.Prime 362865177953 := by
  apply lucas_primality 362865177953 (3 : ZMod 362865177953)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11339536811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11339536811, 1)] : List FactorBlock).map factorBlockValue).prod) = 362865177953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_11339536811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 362865177953) ^ 181432588976 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 362865177953) ^ 32 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_388408415123 : Nat.Prime 388408415123 := by
  apply lucas_primality 388408415123 (2 : ZMod 388408415123)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (479, 1), (1213, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (479, 1), (1213, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) = 388408415123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_479
      · exact prime_twentyTwoT_1213
      · exact prime_twentyTwoT_3673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 388408415123) ^ 194204207561 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 388408415123) ^ 55486916446 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 388408415123) ^ 29877570394 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 388408415123) ^ 810873518 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 388408415123) ^ 320204794 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 388408415123) ^ 105746914 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_17
      · exact prime_twentyTwoT_397
      · exact prime_twentyTwoT_2531
      · exact prime_twentyTwoT_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_531914489033 : Nat.Prime 531914489033 := by
  apply lucas_primality 531914489033 (3 : ZMod 531914489033)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (157, 1), (557, 1), (760321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (157, 1), (557, 1), (760321, 1)] : List FactorBlock).map factorBlockValue).prod) = 531914489033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_157
      · exact prime_twentyTwoT_557
      · exact prime_twentyTwoT_760321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 531914489033) ^ 265957244516 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 531914489033) ^ 3387990376 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 531914489033) ^ 954963176 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 531914489033) ^ 699592 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_553872845191 : Nat.Prime 553872845191 := by
  apply lucas_primality 553872845191 (3 : ZMod 553872845191)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (10159, 1), (259621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (10159, 1), (259621, 1)] : List FactorBlock).map factorBlockValue).prod) = 553872845191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_10159
      · exact prime_twentyTwoT_259621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 553872845191) ^ 276936422595 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 553872845191) ^ 184624281730 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 553872845191) ^ 110774569038 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 553872845191) ^ 79124692170 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 553872845191) ^ 54520410 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 553872845191) ^ 2133390 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_756321939917 : Nat.Prime 756321939917 := by
  apply lucas_primality 756321939917 (2 : ZMod 756321939917)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (18077, 1), (10459727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (18077, 1), (10459727, 1)] : List FactorBlock).map factorBlockValue).prod) = 756321939917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_18077
      · exact prime_twentyTwoT_10459727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 756321939917) ^ 378160969958 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 756321939917) ^ 41838908 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 756321939917) ^ 72308 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_792993323477 : Nat.Prime 792993323477 := by
  apply lucas_primality 792993323477 (2 : ZMod 792993323477)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (739, 1), (1307, 1), (205253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (739, 1), (1307, 1), (205253, 1)] : List FactorBlock).map factorBlockValue).prod) = 792993323477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_739
      · exact prime_twentyTwoT_1307
      · exact prime_twentyTwoT_205253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 792993323477) ^ 396496661738 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 1073062684 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 606727868 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 3863492 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_961255552021 : Nat.Prime 961255552021 := by
  apply lucas_primality 961255552021 (6 : ZMod 961255552021)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (89, 1), (180010403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (89, 1), (180010403, 1)] : List FactorBlock).map factorBlockValue).prod) = 961255552021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_89
      · exact prime_twentyTwoT_180010403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 961255552021) ^ 480627776010 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 961255552021) ^ 320418517340 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 961255552021) ^ 192251110404 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 961255552021) ^ 10800624180 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 961255552021) ^ 5340 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_981356944319 : Nat.Prime 981356944319 := by
  apply lucas_primality 981356944319 (11 : ZMod 981356944319)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (157, 1), (24608981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (157, 1), (24608981, 1)] : List FactorBlock).map factorBlockValue).prod) = 981356944319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_127
      · exact prime_twentyTwoT_157
      · exact prime_twentyTwoT_24608981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 981356944319) ^ 490678472159 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 981356944319) ^ 7727220034 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 981356944319) ^ 6250681174 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 981356944319) ^ 39878 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1065061968151 : Nat.Prime 1065061968151 := by
  apply lucas_primality 1065061968151 (6 : ZMod 1065061968151)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (137, 1), (2557, 1), (20269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (137, 1), (2557, 1), (20269, 1)] : List FactorBlock).map factorBlockValue).prod) = 1065061968151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_137
      · exact prime_twentyTwoT_2557
      · exact prime_twentyTwoT_20269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1065061968151) ^ 532530984075 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1065061968151) ^ 355020656050 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1065061968151) ^ 213012393630 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1065061968151) ^ 7774174950 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1065061968151) ^ 416527950 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1065061968151) ^ 52546350 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1143045681439 : Nat.Prime 1143045681439 := by
  apply lucas_primality 1143045681439 (6 : ZMod 1143045681439)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (190507613573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (190507613573, 1)] : List FactorBlock).map factorBlockValue).prod) = 1143045681439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_190507613573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1143045681439) ^ 571522840719 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143045681439) ^ 381015227146 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143045681439) ^ 6 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1327893142907 : Nat.Prime 1327893142907 := by
  apply lucas_primality 1327893142907 (2 : ZMod 1327893142907)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (53, 1), (1138844891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (53, 1), (1138844891, 1)] : List FactorBlock).map factorBlockValue).prod) = 1327893142907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_53
      · exact prime_twentyTwoT_1138844891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1327893142907) ^ 663946571453 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1327893142907) ^ 120717558446 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1327893142907) ^ 25054587602 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1327893142907) ^ 1166 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_35279
      · exact prime_twentyTwoT_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1754527902319 : Nat.Prime 1754527902319 := by
  apply lucas_primality 1754527902319 (3 : ZMod 1754527902319)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (719, 1), (2819, 1), (48091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (719, 1), (2819, 1), (48091, 1)] : List FactorBlock).map factorBlockValue).prod) = 1754527902319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_719
      · exact prime_twentyTwoT_2819
      · exact prime_twentyTwoT_48091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1754527902319) ^ 877263951159 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1754527902319) ^ 584842634106 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1754527902319) ^ 2440233522 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1754527902319) ^ 622393722 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1754527902319) ^ 36483498 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1837922801387 : Nat.Prime 1837922801387 := by
  apply lucas_primality 1837922801387 (2 : ZMod 1837922801387)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (131280200099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (131280200099, 1)] : List FactorBlock).map factorBlockValue).prod) = 1837922801387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_131280200099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1837922801387) ^ 918961400693 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1837922801387) ^ 262560400198 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1837922801387) ^ 14 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1987018880687 : Nat.Prime 1987018880687 := by
  apply lucas_primality 1987018880687 (5 : ZMod 1987018880687)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (141929920049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (141929920049, 1)] : List FactorBlock).map factorBlockValue).prod) = 1987018880687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_141929920049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1987018880687) ^ 993509440343 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1987018880687) ^ 283859840098 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1987018880687) ^ 14 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2223638394763 : Nat.Prime 2223638394763 := by
  apply lucas_primality 2223638394763 (2 : ZMod 2223638394763)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (282959, 1), (1309753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (282959, 1), (1309753, 1)] : List FactorBlock).map factorBlockValue).prod) = 2223638394763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_282959
      · exact prime_twentyTwoT_1309753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2223638394763) ^ 1111819197381 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2223638394763) ^ 741212798254 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2223638394763) ^ 7858518 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2223638394763) ^ 1697754 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2238205449829 : Nat.Prime 2238205449829 := by
  apply lucas_primality 2238205449829 (2 : ZMod 2238205449829)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (947, 1), (3907, 1), (50411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (947, 1), (3907, 1), (50411, 1)] : List FactorBlock).map factorBlockValue).prod) = 2238205449829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_947
      · exact prime_twentyTwoT_3907
      · exact prime_twentyTwoT_50411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2238205449829) ^ 1119102724914 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2238205449829) ^ 746068483276 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2238205449829) ^ 2363469324 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2238205449829) ^ 572870604 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2238205449829) ^ 44399148 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2340867574039 : Nat.Prime 2340867574039 := by
  apply lucas_primality 2340867574039 (3 : ZMod 2340867574039)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (174157, 1), (320027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (174157, 1), (320027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2340867574039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_174157
      · exact prime_twentyTwoT_320027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2340867574039) ^ 1170433787019 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2340867574039) ^ 780289191346 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2340867574039) ^ 334409653434 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2340867574039) ^ 13441134 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2340867574039) ^ 7314594 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2796680117807 : Nat.Prime 2796680117807 := by
  apply lucas_primality 2796680117807 (5 : ZMod 2796680117807)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (157, 1), (593, 1), (246223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (157, 1), (593, 1), (246223, 1)] : List FactorBlock).map factorBlockValue).prod) = 2796680117807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_61
      · exact prime_twentyTwoT_157
      · exact prime_twentyTwoT_593
      · exact prime_twentyTwoT_246223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2796680117807) ^ 1398340058903 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2796680117807) ^ 45847215046 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2796680117807) ^ 17813249158 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2796680117807) ^ 4716155342 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2796680117807) ^ 11358322 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2867706713387 : Nat.Prime 2867706713387 := by
  apply lucas_primality 2867706713387 (2 : ZMod 2867706713387)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (631, 1), (1637, 1), (60353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (631, 1), (1637, 1), (60353, 1)] : List FactorBlock).map factorBlockValue).prod) = 2867706713387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_23
      · exact prime_twentyTwoT_631
      · exact prime_twentyTwoT_1637
      · exact prime_twentyTwoT_60353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2867706713387) ^ 1433853356693 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2867706713387) ^ 124682900582 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2867706713387) ^ 4544701606 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2867706713387) ^ 1751806178 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2867706713387) ^ 47515562 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2909674311721 : Nat.Prime 2909674311721 := by
  apply lucas_primality 2909674311721 (13 : ZMod 2909674311721)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (191, 1), (11540831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (191, 1), (11540831, 1)] : List FactorBlock).map factorBlockValue).prod) = 2909674311721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_191
      · exact prime_twentyTwoT_11540831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2909674311721) ^ 1454837155860 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 969891437240 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 581934862344 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 264515846520 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 15233896920 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 252120 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_3496992739049 : Nat.Prime 3496992739049 := by
  apply lucas_primality 3496992739049 (3 : ZMod 3496992739049)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (103, 1), (98695889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (103, 1), (98695889, 1)] : List FactorBlock).map factorBlockValue).prod) = 3496992739049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_43
      · exact prime_twentyTwoT_103
      · exact prime_twentyTwoT_98695889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3496992739049) ^ 1748496369524 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3496992739049) ^ 81325412536 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3496992739049) ^ 33951385816 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3496992739049) ^ 35432 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_3842353464491 : Nat.Prime 3842353464491 := by
  apply lucas_primality 3842353464491 (2 : ZMod 3842353464491)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (433, 1), (46704187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (433, 1), (46704187, 1)] : List FactorBlock).map factorBlockValue).prod) = 3842353464491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_433
      · exact prime_twentyTwoT_46704187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3842353464491) ^ 1921176732245 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3842353464491) ^ 768470692898 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3842353464491) ^ 202229129710 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3842353464491) ^ 8873795530 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3842353464491) ^ 82270 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_3850926034597 : Nat.Prime 3850926034597 := by
  apply lucas_primality 3850926034597 (5 : ZMod 3850926034597)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (83, 1), (3866391601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (83, 1), (3866391601, 1)] : List FactorBlock).map factorBlockValue).prod) = 3850926034597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_83
      · exact prime_twentyTwoT_3866391601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3850926034597) ^ 1925463017298 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 3850926034597) ^ 1283642011532 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 3850926034597) ^ 46396699212 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 3850926034597) ^ 996 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_4367130462439 : Nat.Prime 4367130462439 := by
  apply lucas_primality 4367130462439 (6 : ZMod 4367130462439)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (163, 1), (4465368571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (163, 1), (4465368571, 1)] : List FactorBlock).map factorBlockValue).prod) = 4367130462439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_163
      · exact prime_twentyTwoT_4465368571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 4367130462439) ^ 2183565231219 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 4367130462439) ^ 1455710154146 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 4367130462439) ^ 26792211426 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 4367130462439) ^ 978 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_4446557982871 : Nat.Prime 4446557982871 := by
  apply lucas_primality 4446557982871 (3 : ZMod 4446557982871)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (73, 1), (1381, 1), (1470233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (73, 1), (1381, 1), (1470233, 1)] : List FactorBlock).map factorBlockValue).prod) = 4446557982871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_73
      · exact prime_twentyTwoT_1381
      · exact prime_twentyTwoT_1470233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4446557982871) ^ 2223278991435 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4446557982871) ^ 1482185994290 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4446557982871) ^ 889311596574 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4446557982871) ^ 60911753190 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4446557982871) ^ 3219810270 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4446557982871) ^ 3024390 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_4819414370321 : Nat.Prime 4819414370321 := by
  apply lucas_primality 4819414370321 (3 : ZMod 4819414370321)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 1), (17, 1), (2081, 1), (154807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 1), (17, 1), (2081, 1), (154807, 1)] : List FactorBlock).map factorBlockValue).prod) = 4819414370321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_17
      · exact prime_twentyTwoT_2081
      · exact prime_twentyTwoT_154807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4819414370321) ^ 2409707185160 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 963882874064 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 438128579120 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 283494962960 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 2315912720 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 31131760 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_12146595562733 : Nat.Prime 12146595562733 := by
  apply lucas_primality 12146595562733 (2 : ZMod 12146595562733)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (21846394897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (21846394897, 1)] : List FactorBlock).map factorBlockValue).prod) = 12146595562733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_139
      · exact prime_twentyTwoT_21846394897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12146595562733) ^ 6073297781366 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 12146595562733) ^ 87385579588 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 12146595562733) ^ 556 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_17782245395071 : Nat.Prime 17782245395071 := by
  apply lucas_primality 17782245395071 (6 : ZMod 17782245395071)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (45595501013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (45595501013, 1)] : List FactorBlock).map factorBlockValue).prod) = 17782245395071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_45595501013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17782245395071) ^ 8891122697535 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 17782245395071) ^ 5927415131690 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 17782245395071) ^ 3556449079014 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 17782245395071) ^ 1367865030390 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 17782245395071) ^ 390 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_38246275718023 : Nat.Prime 38246275718023 := by
  apply lucas_primality 38246275718023 (3 : ZMod 38246275718023)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1297, 1), (4914710321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1297, 1), (4914710321, 1)] : List FactorBlock).map factorBlockValue).prod) = 38246275718023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_1297
      · exact prime_twentyTwoT_4914710321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 38246275718023) ^ 19123137859011 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 38246275718023) ^ 12748758572674 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 38246275718023) ^ 29488261926 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 38246275718023) ^ 7782 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_42143426280649 : Nat.Prime 42143426280649 := by
  apply lucas_primality 42143426280649 (13 : ZMod 42143426280649)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 1), (11, 1), (2533876039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 1), (11, 1), (2533876039, 1)] : List FactorBlock).map factorBlockValue).prod) = 42143426280649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_2533876039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 42143426280649) ^ 21071713140324 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 42143426280649) ^ 14047808760216 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 42143426280649) ^ 6020489468664 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 42143426280649) ^ 3831220570968 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 42143426280649) ^ 16632 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_52986933480497 : Nat.Prime 52986933480497 := by
  apply lucas_primality 52986933480497 (3 : ZMod 52986933480497)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3559, 1), (930509509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3559, 1), (930509509, 1)] : List FactorBlock).map factorBlockValue).prod) = 52986933480497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3559
      · exact prime_twentyTwoT_930509509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 52986933480497) ^ 26493466740248 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 52986933480497) ^ 14888152144 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 52986933480497) ^ 56944 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_56020723162777 : Nat.Prime 56020723162777 := by
  apply lucas_primality 56020723162777 (5 : ZMod 56020723162777)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (271, 1), (2871090773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (271, 1), (2871090773, 1)] : List FactorBlock).map factorBlockValue).prod) = 56020723162777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_271
      · exact prime_twentyTwoT_2871090773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 56020723162777) ^ 28010361581388 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 56020723162777) ^ 18673574387592 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 56020723162777) ^ 206718535656 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 56020723162777) ^ 19512 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_60062573936429 : Nat.Prime 60062573936429 := by
  apply lucas_primality 60062573936429 (10 : ZMod 60062573936429)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (8147, 1), (263298383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (8147, 1), (263298383, 1)] : List FactorBlock).map factorBlockValue).prod) = 60062573936429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_8147
      · exact prime_twentyTwoT_263298383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 60062573936429) ^ 30031286968214 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (10 : ZMod 60062573936429) ^ 8580367705204 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (10 : ZMod 60062573936429) ^ 7372354724 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (10 : ZMod 60062573936429) ^ 228116 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_104811131098537 : Nat.Prime 104811131098537 := by
  apply lucas_primality 104811131098537 (5 : ZMod 104811131098537)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4367130462439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4367130462439, 1)] : List FactorBlock).map factorBlockValue).prod) = 104811131098537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_4367130462439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 104811131098537) ^ 52405565549268 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 104811131098537) ^ 34937043699512 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 104811131098537) ^ 24 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_110784210377741 : Nat.Prime 110784210377741 := by
  apply lucas_primality 110784210377741 (7 : ZMod 110784210377741)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19841, 1), (279180007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19841, 1), (279180007, 1)] : List FactorBlock).map factorBlockValue).prod) = 110784210377741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_19841
      · exact prime_twentyTwoT_279180007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 110784210377741) ^ 55392105188870 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 110784210377741) ^ 22156842075548 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 110784210377741) ^ 5583600140 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 110784210377741) ^ 396820 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_120125147872859 : Nat.Prime 120125147872859 := by
  apply lucas_primality 120125147872859 (2 : ZMod 120125147872859)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (60062573936429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (60062573936429, 1)] : List FactorBlock).map factorBlockValue).prod) = 120125147872859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_60062573936429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 120125147872859) ^ 60062573936429 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 120125147872859) ^ 2 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_121302904891543 : Nat.Prime 121302904891543 := by
  apply lucas_primality 121302904891543 (5 : ZMod 121302904891543)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1837922801387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1837922801387, 1)] : List FactorBlock).map factorBlockValue).prod) = 121302904891543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_1837922801387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 121302904891543) ^ 60651452445771 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 121302904891543) ^ 40434301630514 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 121302904891543) ^ 11027536808322 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 121302904891543) ^ 66 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_269887204737977 : Nat.Prime 269887204737977 := by
  apply lucas_primality 269887204737977 (3 : ZMod 269887204737977)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (4819414370321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (4819414370321, 1)] : List FactorBlock).map factorBlockValue).prod) = 269887204737977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_4819414370321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 269887204737977) ^ 134943602368988 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 269887204737977) ^ 38555314962568 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 269887204737977) ^ 56 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_281547015287347 : Nat.Prime 281547015287347 := by
  apply lucas_primality 281547015287347 (2 : ZMod 281547015287347)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (941, 1), (12743, 1), (1304419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (941, 1), (12743, 1), (1304419, 1)] : List FactorBlock).map factorBlockValue).prod) = 281547015287347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_941
      · exact prime_twentyTwoT_12743
      · exact prime_twentyTwoT_1304419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 281547015287347) ^ 140773507643673 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 281547015287347) ^ 93849005095782 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 281547015287347) ^ 299199803706 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 281547015287347) ^ 22094249022 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 281547015287347) ^ 215840934 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_326588998557317 : Nat.Prime 326588998557317 := by
  apply lucas_primality 326588998557317 (2 : ZMod 326588998557317)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1217, 1), (2129, 1), (2864723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1217, 1), (2129, 1), (2864723, 1)] : List FactorBlock).map factorBlockValue).prod) = 326588998557317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_1217
      · exact prime_twentyTwoT_2129
      · exact prime_twentyTwoT_2864723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 326588998557317) ^ 163294499278658 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 326588998557317) ^ 29689908959756 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 326588998557317) ^ 268355791748 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 326588998557317) ^ 153400187204 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 326588998557317) ^ 114003692 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_376537177183483 : Nat.Prime 376537177183483 := by
  apply lucas_primality 376537177183483 (2 : ZMod 376537177183483)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod) = 376537177183483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_35853943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 376537177183483) ^ 188268588591741 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 125512392394494 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 53791025311926 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 10501974 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_379936683161863 : Nat.Prime 379936683161863 := by
  apply lucas_primality 379936683161863 (6 : ZMod 379936683161863)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1279, 1), (49509601663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1279, 1), (49509601663, 1)] : List FactorBlock).map factorBlockValue).prod) = 379936683161863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_1279
      · exact prime_twentyTwoT_49509601663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 379936683161863) ^ 189968341580931 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 379936683161863) ^ 126645561053954 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 379936683161863) ^ 297057609978 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 379936683161863) ^ 7674 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_385610041946069 : Nat.Prime 385610041946069 := by
  apply lucas_primality 385610041946069 (2 : ZMod 385610041946069)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8951, 1), (10770026867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8951, 1), (10770026867, 1)] : List FactorBlock).map factorBlockValue).prod) = 385610041946069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_8951
      · exact prime_twentyTwoT_10770026867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 385610041946069) ^ 192805020973034 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 385610041946069) ^ 43080107468 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 385610041946069) ^ 35804 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_403073885242069 : Nat.Prime 403073885242069 := by
  apply lucas_primality 403073885242069 (2 : ZMod 403073885242069)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (627787, 1), (53504597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (627787, 1), (53504597, 1)] : List FactorBlock).map factorBlockValue).prod) = 403073885242069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_627787
      · exact prime_twentyTwoT_53504597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 403073885242069) ^ 201536942621034 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 403073885242069) ^ 134357961747356 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 403073885242069) ^ 642055164 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 403073885242069) ^ 7533444 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_433030813401061 : Nat.Prime 433030813401061 := by
  apply lucas_primality 433030813401061 (2 : ZMod 433030813401061)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (61, 1), (71, 1), (4937, 1), (16073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (61, 1), (71, 1), (4937, 1), (16073, 1)] : List FactorBlock).map factorBlockValue).prod) = 433030813401061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_61
      · exact prime_twentyTwoT_71
      · exact prime_twentyTwoT_4937
      · exact prime_twentyTwoT_16073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 433030813401061) ^ 216515406700530 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 433030813401061) ^ 144343604467020 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 433030813401061) ^ 86606162680212 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 433030813401061) ^ 61861544771580 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 433030813401061) ^ 7098865793460 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 433030813401061) ^ 6099025540860 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 433030813401061) ^ 87711325380 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 433030813401061) ^ 26941505220 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_456818736397697 : Nat.Prime 456818736397697 := by
  apply lucas_primality 456818736397697 (3 : ZMod 456818736397697)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod) = 456818736397697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_67
      · exact prime_twentyTwoT_28807
      · exact prime_twentyTwoT_1849103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 456818736397697) ^ 228409368198848 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 6818190095488 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 15857907328 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 247048832 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_519686014726079 : Nat.Prime 519686014726079 := by
  apply lucas_primality 519686014726079 (11 : ZMod 519686014726079)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (379, 1), (624277, 1), (1098233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (379, 1), (624277, 1), (1098233, 1)] : List FactorBlock).map factorBlockValue).prod) = 519686014726079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_379
      · exact prime_twentyTwoT_624277
      · exact prime_twentyTwoT_1098233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 519686014726079) ^ 259843007363039 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 519686014726079) ^ 1371203205082 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 519686014726079) ^ 832460614 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 519686014726079) ^ 473201966 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_621911721757133 : Nat.Prime 621911721757133 := by
  apply lucas_primality 621911721757133 (2 : ZMod 621911721757133)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1123, 1), (138448735921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1123, 1), (138448735921, 1)] : List FactorBlock).map factorBlockValue).prod) = 621911721757133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_1123
      · exact prime_twentyTwoT_138448735921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 621911721757133) ^ 310955860878566 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 621911721757133) ^ 553794943684 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 621911721757133) ^ 4492 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_988642159474447 : Nat.Prime 988642159474447 := by
  apply lucas_primality 988642159474447 (3 : ZMod 988642159474447)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5869, 1), (8669, 1), (1079527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5869, 1), (8669, 1), (1079527, 1)] : List FactorBlock).map factorBlockValue).prod) = 988642159474447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5869
      · exact prime_twentyTwoT_8669
      · exact prime_twentyTwoT_1079527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 988642159474447) ^ 494321079737223 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 988642159474447) ^ 329547386491482 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 988642159474447) ^ 168451552134 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 988642159474447) ^ 114043391334 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 988642159474447) ^ 915810498 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1012564812501629 : Nat.Prime 1012564812501629 := by
  apply lucas_primality 1012564812501629 (2 : ZMod 1012564812501629)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1883407, 1), (134406001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1883407, 1), (134406001, 1)] : List FactorBlock).map factorBlockValue).prod) = 1012564812501629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_1883407
      · exact prime_twentyTwoT_134406001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1012564812501629) ^ 506282406250814 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1012564812501629) ^ 537624004 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1012564812501629) ^ 7533628 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1132865085569267 : Nat.Prime 1132865085569267 := by
  apply lucas_primality 1132865085569267 (2 : ZMod 1132865085569267)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (223, 1), (362865177953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (223, 1), (362865177953, 1)] : List FactorBlock).map factorBlockValue).prod) = 1132865085569267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_223
      · exact prime_twentyTwoT_362865177953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1132865085569267) ^ 566432542784633 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1132865085569267) ^ 161837869367038 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1132865085569267) ^ 5080112491342 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1132865085569267) ^ 3122 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1384711894151563 : Nat.Prime 1384711894151563 := by
  apply lucas_primality 1384711894151563 (2 : ZMod 1384711894151563)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (12146595562733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (12146595562733, 1)] : List FactorBlock).map factorBlockValue).prod) = 1384711894151563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_12146595562733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1384711894151563) ^ 692355947075781 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1384711894151563) ^ 461570631383854 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1384711894151563) ^ 72879573376398 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1384711894151563) ^ 114 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1430587384194481 : Nat.Prime 1430587384194481 := by
  apply lucas_primality 1430587384194481 (13 : ZMod 1430587384194481)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (271, 1), (21995500987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (271, 1), (21995500987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1430587384194481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_271
      · exact prime_twentyTwoT_21995500987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1430587384194481) ^ 715293692097240 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 1430587384194481) ^ 476862461398160 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 1430587384194481) ^ 286117476838896 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 1430587384194481) ^ 5278920236880 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (13 : ZMod 1430587384194481) ^ 65040 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_41
      · exact prime_twentyTwoT_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2093164517926973 : Nat.Prime 2093164517926973 := by
  apply lucas_primality 2093164517926973 (2 : ZMod 2093164517926973)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 2), (269, 1), (330443381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 2), (269, 1), (330443381, 1)] : List FactorBlock).map factorBlockValue).prod) = 2093164517926973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_29
      · exact prime_twentyTwoT_269
      · exact prime_twentyTwoT_330443381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2093164517926973) ^ 1046582258963486 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2093164517926973) ^ 299023502560996 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2093164517926973) ^ 72178086825068 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2093164517926973) ^ 7781280735788 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2093164517926973) ^ 6334412 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2192725397572529 : Nat.Prime 2192725397572529 := by
  apply lucas_primality 2192725397572529 (3 : ZMod 2192725397572529)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (13, 2), (59, 1), (421, 1), (4663859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (13, 2), (59, 1), (421, 1), (4663859, 1)] : List FactorBlock).map factorBlockValue).prod) = 2192725397572529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_59
      · exact prime_twentyTwoT_421
      · exact prime_twentyTwoT_4663859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2192725397572529) ^ 1096362698786264 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2192725397572529) ^ 313246485367504 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2192725397572529) ^ 168671184428656 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2192725397572529) ^ 37164837246992 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2192725397572529) ^ 5208373865968 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2192725397572529) ^ 470152592 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_5832880731578591 : Nat.Prime 5832880731578591 := by
  apply lucas_primality 5832880731578591 (11 : ZMod 5832880731578591)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (117193, 1), (4977157963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (117193, 1), (4977157963, 1)] : List FactorBlock).map factorBlockValue).prod) = 5832880731578591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_117193
      · exact prime_twentyTwoT_4977157963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 5832880731578591) ^ 2916440365789295 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 5832880731578591) ^ 1166576146315718 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 5832880731578591) ^ 49771579630 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 5832880731578591) ^ 1171930 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_6078986930589809 : Nat.Prime 6078986930589809 := by
  apply lucas_primality 6078986930589809 (3 : ZMod 6078986930589809)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (379936683161863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (379936683161863, 1)] : List FactorBlock).map factorBlockValue).prod) = 6078986930589809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_379936683161863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 6078986930589809) ^ 3039493465294904 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 6078986930589809) ^ 16 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_6395462309567759 : Nat.Prime 6395462309567759 := by
  apply lucas_primality 6395462309567759 (7 : ZMod 6395462309567759)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod) = 6395462309567759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_456818736397697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6395462309567759) ^ 3197731154783879 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 913637472795394 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 14 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_8583524305166887 : Nat.Prime 8583524305166887 := by
  apply lucas_primality 8583524305166887 (6 : ZMod 8583524305166887)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1430587384194481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1430587384194481, 1)] : List FactorBlock).map factorBlockValue).prod) = 8583524305166887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_1430587384194481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 8583524305166887) ^ 4291762152583443 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 8583524305166887) ^ 2861174768388962 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 8583524305166887) ^ 6 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_8899091597863531 : Nat.Prime 8899091597863531 := by
  apply lucas_primality 8899091597863531 (2 : ZMod 8899091597863531)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (661, 1), (2311, 1), (2887, 1), (3203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (661, 1), (2311, 1), (2887, 1), (3203, 1)] : List FactorBlock).map factorBlockValue).prod) = 8899091597863531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_661
      · exact prime_twentyTwoT_2311
      · exact prime_twentyTwoT_2887
      · exact prime_twentyTwoT_3203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8899091597863531) ^ 4449545798931765 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8899091597863531) ^ 2966363865954510 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8899091597863531) ^ 1779818319572706 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8899091597863531) ^ 1271298799694790 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8899091597863531) ^ 13463073521730 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8899091597863531) ^ 3850753612230 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8899091597863531) ^ 3082470245190 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8899091597863531) ^ 2778361410510 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_10132269515533267 : Nat.Prime 10132269515533267 := by
  apply lucas_primality 10132269515533267 (2 : ZMod 10132269515533267)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (36899, 1), (2692104817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (36899, 1), (2692104817, 1)] : List FactorBlock).map factorBlockValue).prod) = 10132269515533267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_17
      · exact prime_twentyTwoT_36899
      · exact prime_twentyTwoT_2692104817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10132269515533267) ^ 5066134757766633 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10132269515533267) ^ 3377423171844422 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10132269515533267) ^ 596015853854898 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10132269515533267) ^ 274594691334 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10132269515533267) ^ 3763698 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_10279120799235109 : Nat.Prime 10279120799235109 := by
  apply lucas_primality 10279120799235109 (6 : ZMod 10279120799235109)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (347, 1), (827, 1), (28687, 1), (104053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (347, 1), (827, 1), (28687, 1), (104053, 1)] : List FactorBlock).map factorBlockValue).prod) = 10279120799235109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_347
      · exact prime_twentyTwoT_827
      · exact prime_twentyTwoT_28687
      · exact prime_twentyTwoT_104053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10279120799235109) ^ 5139560399617554 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 3426373599745036 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 29622826510764 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 12429408463404 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 358319824284 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 98787356436 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_11696987923719619 : Nat.Prime 11696987923719619 := by
  apply lucas_primality 11696987923719619 (2 : ZMod 11696987923719619)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (35509, 1), (4223193659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (35509, 1), (4223193659, 1)] : List FactorBlock).map factorBlockValue).prod) = 11696987923719619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_35509
      · exact prime_twentyTwoT_4223193659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11696987923719619) ^ 5848493961859809 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 11696987923719619) ^ 3898995974573206 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 11696987923719619) ^ 899768301824586 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 11696987923719619) ^ 329409105402 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 11696987923719619) ^ 2769702 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_19595339913439021 : Nat.Prime 19595339913439021 := by
  apply lucas_primality 19595339913439021 (11 : ZMod 19595339913439021)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (326588998557317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (326588998557317, 1)] : List FactorBlock).map factorBlockValue).prod) = 19595339913439021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_326588998557317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 19595339913439021) ^ 9797669956719510 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 19595339913439021) ^ 6531779971146340 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 19595339913439021) ^ 3919067982687804 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (11 : ZMod 19595339913439021) ^ 60 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_21209092332463747 : Nat.Prime 21209092332463747 := by
  apply lucas_primality 21209092332463747 (2 : ZMod 21209092332463747)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (2367523, 1), (165895313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (2367523, 1), (165895313, 1)] : List FactorBlock).map factorBlockValue).prod) = 21209092332463747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_2367523
      · exact prime_twentyTwoT_165895313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21209092332463747) ^ 10604546166231873 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 21209092332463747) ^ 7069697444154582 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 21209092332463747) ^ 8958346902 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 21209092332463747) ^ 127846242 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_30492110377557209 : Nat.Prime 30492110377557209 := by
  apply lucas_primality 30492110377557209 (3 : ZMod 30492110377557209)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (1637, 1), (6529, 1), (11503777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (1637, 1), (6529, 1), (11503777, 1)] : List FactorBlock).map factorBlockValue).prod) = 30492110377557209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_31
      · exact prime_twentyTwoT_1637
      · exact prime_twentyTwoT_6529
      · exact prime_twentyTwoT_11503777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30492110377557209) ^ 15246055188778604 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 30492110377557209) ^ 983616463792168 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 30492110377557209) ^ 18626823688184 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 30492110377557209) ^ 4670257371352 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 30492110377557209) ^ 2650617304 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_46093020050440787 : Nat.Prime 46093020050440787 := by
  apply lucas_primality 46093020050440787 (2 : ZMod 46093020050440787)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (73, 1), (4446557982871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (73, 1), (4446557982871, 1)] : List FactorBlock).map factorBlockValue).prod) = 46093020050440787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_71
      · exact prime_twentyTwoT_73
      · exact prime_twentyTwoT_4446557982871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46093020050440787) ^ 23046510025220393 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 46093020050440787) ^ 649197465499166 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 46093020050440787) ^ 631411233567682 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 46093020050440787) ^ 10366 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_46850588275089773 : Nat.Prime 46850588275089773 := by
  apply lucas_primality 46850588275089773 (2 : ZMod 46850588275089773)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (157, 1), (3011, 1), (313629971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (157, 1), (3011, 1), (313629971, 1)] : List FactorBlock).map factorBlockValue).prod) = 46850588275089773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_79
      · exact prime_twentyTwoT_157
      · exact prime_twentyTwoT_3011
      · exact prime_twentyTwoT_313629971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 46850588275089773) ^ 23425294137544886 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 46850588275089773) ^ 593045421203668 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 46850588275089773) ^ 298411390287196 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 46850588275089773) ^ 15559810121252 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 46850588275089773) ^ 149381732 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_89292073564459247 : Nat.Prime 89292073564459247 := by
  apply lucas_primality 89292073564459247 (5 : ZMod 89292073564459247)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (31, 1), (110784210377741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (31, 1), (110784210377741, 1)] : List FactorBlock).map factorBlockValue).prod) = 89292073564459247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_31
      · exact prime_twentyTwoT_110784210377741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 89292073564459247) ^ 44646036782229623 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 89292073564459247) ^ 6868621043419942 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 89292073564459247) ^ 2880389469821266 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 89292073564459247) ^ 806 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_111627758947967783 : Nat.Prime 111627758947967783 := by
  apply lucas_primality 111627758947967783 (10 : ZMod 111627758947967783)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (631, 1), (358109545763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (631, 1), (358109545763, 1)] : List FactorBlock).map factorBlockValue).prod) = 111627758947967783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_631
      · exact prime_twentyTwoT_358109545763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 111627758947967783) ^ 55813879473983891 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (10 : ZMod 111627758947967783) ^ 8586750688305214 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (10 : ZMod 111627758947967783) ^ 5875145207787778 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (10 : ZMod 111627758947967783) ^ 176906115606922 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (10 : ZMod 111627758947967783) ^ 311714 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_140392491357773839 : Nat.Prime 140392491357773839 := by
  apply lucas_primality 140392491357773839 (6 : ZMod 140392491357773839)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (1559, 1), (14423, 1), (22140787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (1559, 1), (14423, 1), (22140787, 1)] : List FactorBlock).map factorBlockValue).prod) = 140392491357773839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_47
      · exact prime_twentyTwoT_1559
      · exact prime_twentyTwoT_14423
      · exact prime_twentyTwoT_22140787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 140392491357773839) ^ 70196245678886919 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392491357773839) ^ 46797497119257946 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392491357773839) ^ 2987074284207954 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392491357773839) ^ 90052912994082 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392491357773839) ^ 9733931315106 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392491357773839) ^ 6340898874 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_261838724217232711 : Nat.Prime 261838724217232711 := by
  apply lucas_primality 261838724217232711 (6 : ZMod 261838724217232711)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (281547015287347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (281547015287347, 1)] : List FactorBlock).map factorBlockValue).prod) = 261838724217232711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_31
      · exact prime_twentyTwoT_281547015287347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 261838724217232711) ^ 130919362108616355 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 261838724217232711) ^ 87279574739077570 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 261838724217232711) ^ 52367744843446542 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 261838724217232711) ^ 8446410458620410 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 261838724217232711) ^ 930 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_263505991609941173 : Nat.Prime 263505991609941173 := by
  apply lucas_primality 263505991609941173 (2 : ZMod 263505991609941173)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (11068193, 1), (61359533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (11068193, 1), (61359533, 1)] : List FactorBlock).map factorBlockValue).prod) = 263505991609941173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_97
      · exact prime_twentyTwoT_11068193
      · exact prime_twentyTwoT_61359533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 263505991609941173) ^ 131752995804970586 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 263505991609941173) ^ 2716556614535476 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 263505991609941173) ^ 23807498804 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 263505991609941173) ^ 4294458884 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_374376818878815937 : Nat.Prime 374376818878815937 := by
  apply lucas_primality 374376818878815937 (5 : ZMod 374376818878815937)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (35569, 1), (54819625657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (35569, 1), (54819625657, 1)] : List FactorBlock).map factorBlockValue).prod) = 374376818878815937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_35569
      · exact prime_twentyTwoT_54819625657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 374376818878815937) ^ 187188409439407968 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 374376818878815937) ^ 124792272959605312 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 374376818878815937) ^ 10525368126144 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 374376818878815937) ^ 6829248 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_423378269541287941 : Nat.Prime 423378269541287941 := by
  apply lucas_primality 423378269541287941 (21 : ZMod 423378269541287941)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 2), (2887, 1), (132857, 1), (152041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 2), (2887, 1), (132857, 1), (152041, 1)] : List FactorBlock).map factorBlockValue).prod) = 423378269541287941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_2887
      · exact prime_twentyTwoT_132857
      · exact prime_twentyTwoT_152041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 423378269541287941) ^ 211689134770643970 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (21 : ZMod 423378269541287941) ^ 141126089847095980 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (21 : ZMod 423378269541287941) ^ 84675653908257588 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (21 : ZMod 423378269541287941) ^ 38488933594662540 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (21 : ZMod 423378269541287941) ^ 146649902854620 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (21 : ZMod 423378269541287941) ^ 3186721584420 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (21 : ZMod 423378269541287941) ^ 2784632234340 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_29
      · exact prime_twentyTwoT_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_554011756364663489 : Nat.Prime 554011756364663489 := by
  apply lucas_primality 554011756364663489 (3 : ZMod 554011756364663489)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (41, 1), (10691, 1), (19748623057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (41, 1), (10691, 1), (19748623057, 1)] : List FactorBlock).map factorBlockValue).prod) = 554011756364663489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_41
      · exact prime_twentyTwoT_10691
      · exact prime_twentyTwoT_19748623057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 554011756364663489) ^ 277005878182331744 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 554011756364663489) ^ 13512481862552768 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 554011756364663489) ^ 51820386901568 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 554011756364663489) ^ 28053184 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_61717
      · exact prime_twentyTwoT_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_611866157797460743 : Nat.Prime 611866157797460743 := by
  apply lucas_primality 611866157797460743 (5 : ZMod 611866157797460743)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (23, 1), (403073885242069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (23, 1), (403073885242069, 1)] : List FactorBlock).map factorBlockValue).prod) = 611866157797460743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_23
      · exact prime_twentyTwoT_403073885242069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 611866157797460743) ^ 305933078898730371 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 611866157797460743) ^ 203955385932486914 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 611866157797460743) ^ 55624196163405522 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 611866157797460743) ^ 26602876425976554 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 611866157797460743) ^ 1518 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_748110513271031791 : Nat.Prime 748110513271031791 := by
  apply lucas_primality 748110513271031791 (3 : ZMod 748110513271031791)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (4093, 1), (553872845191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (4093, 1), (553872845191, 1)] : List FactorBlock).map factorBlockValue).prod) = 748110513271031791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_4093
      · exact prime_twentyTwoT_553872845191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 748110513271031791) ^ 374055256635515895 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 748110513271031791) ^ 249370171090343930 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 748110513271031791) ^ 149622102654206358 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 748110513271031791) ^ 68010046661002890 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 748110513271031791) ^ 182778038913030 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 748110513271031791) ^ 1350690 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_821350062669399719 : Nat.Prime 821350062669399719 := by
  apply lucas_primality 821350062669399719 (7 : ZMod 821350062669399719)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (28617707, 1), (157696507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (28617707, 1), (157696507, 1)] : List FactorBlock).map factorBlockValue).prod) = 821350062669399719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_28617707
      · exact prime_twentyTwoT_157696507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 821350062669399719) ^ 410675031334699859 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 821350062669399719) ^ 117335723238485674 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 821350062669399719) ^ 63180774051492286 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 821350062669399719) ^ 28700764274 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 821350062669399719) ^ 5208422674 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_826636823185963187 : Nat.Prime 826636823185963187 := by
  apply lucas_primality 826636823185963187 (2 : ZMod 826636823185963187)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (80744533, 1), (5118840821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (80744533, 1), (5118840821, 1)] : List FactorBlock).map factorBlockValue).prod) = 826636823185963187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_80744533
      · exact prime_twentyTwoT_5118840821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 826636823185963187) ^ 413318411592981593 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 826636823185963187) ^ 10237681642 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 826636823185963187) ^ 161489066 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_859806059102301397 : Nat.Prime 859806059102301397 := by
  apply lucas_primality 859806059102301397 (2 : ZMod 859806059102301397)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1279, 1), (56020723162777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1279, 1), (56020723162777, 1)] : List FactorBlock).map factorBlockValue).prod) = 859806059102301397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_1279
      · exact prime_twentyTwoT_56020723162777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 859806059102301397) ^ 429903029551150698 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 859806059102301397) ^ 286602019700767132 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 859806059102301397) ^ 672248677953324 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 859806059102301397) ^ 15348 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_878232026121702859 : Nat.Prime 878232026121702859 := by
  apply lucas_primality 878232026121702859 (2 : ZMod 878232026121702859)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (91432559, 1), (533624659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (91432559, 1), (533624659, 1)] : List FactorBlock).map factorBlockValue).prod) = 878232026121702859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_91432559
      · exact prime_twentyTwoT_533624659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 878232026121702859) ^ 439116013060851429 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 878232026121702859) ^ 292744008707234286 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 878232026121702859) ^ 9605243862 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 878232026121702859) ^ 1645786062 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_932050565158189193 : Nat.Prime 932050565158189193 := by
  apply lucas_primality 932050565158189193 (3 : ZMod 932050565158189193)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (40627, 1), (2867706713387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (40627, 1), (2867706713387, 1)] : List FactorBlock).map factorBlockValue).prod) = 932050565158189193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_40627
      · exact prime_twentyTwoT_2867706713387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 932050565158189193) ^ 466025282579094596 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 932050565158189193) ^ 22941653707096 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 932050565158189193) ^ 325016 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_974357259695558663 : Nat.Prime 974357259695558663 := by
  apply lucas_primality 974357259695558663 (5 : ZMod 974357259695558663)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (11, 1), (18217, 1), (7088013991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (11, 1), (18217, 1), (7088013991, 1)] : List FactorBlock).map factorBlockValue).prod) = 974357259695558663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_18217
      · exact prime_twentyTwoT_7088013991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 974357259695558663) ^ 487178629847779331 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 974357259695558663) ^ 139193894242222666 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 974357259695558663) ^ 88577932699596242 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 974357259695558663) ^ 53486153576086 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 974357259695558663) ^ 137465482 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2143009765547021929 : Nat.Prime 2143009765547021929 := by
  apply lucas_primality 2143009765547021929 (7 : ZMod 2143009765547021929)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (89292073564459247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (89292073564459247, 1)] : List FactorBlock).map factorBlockValue).prod) = 2143009765547021929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_89292073564459247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2143009765547021929) ^ 1071504882773510964 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2143009765547021929) ^ 714336588515673976 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2143009765547021929) ^ 24 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2437165707819947287 : Nat.Prime 2437165707819947287 := by
  apply lucas_primality 2437165707819947287 (3 : ZMod 2437165707819947287)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (19, 1), (43427, 1), (72907, 1), (74201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (19, 1), (43427, 1), (72907, 1), (74201, 1)] : List FactorBlock).map factorBlockValue).prod) = 2437165707819947287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_43427
      · exact prime_twentyTwoT_72907
      · exact prime_twentyTwoT_74201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2437165707819947287) ^ 1218582853909973643 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2437165707819947287) ^ 812388569273315762 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2437165707819947287) ^ 348166529688563898 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2437165707819947287) ^ 187474285216919022 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2437165707819947287) ^ 128271879358944594 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2437165707819947287) ^ 56120977912818 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2437165707819947287) ^ 33428418503298 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2437165707819947287) ^ 32845456366086 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_4497349976643679853 : Nat.Prime 4497349976643679853 := by
  apply lucas_primality 4497349976643679853 (2 : ZMod 4497349976643679853)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (5339791, 1), (2170704469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (5339791, 1), (2170704469, 1)] : List FactorBlock).map factorBlockValue).prod) = 4497349976643679853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_97
      · exact prime_twentyTwoT_5339791
      · exact prime_twentyTwoT_2170704469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4497349976643679853) ^ 2248674988321839926 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4497349976643679853) ^ 46364432748903916 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4497349976643679853) ^ 842233333972 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4497349976643679853) ^ 2071838908 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_4874540587086777007 : Nat.Prime 4874540587086777007 := by
  apply lucas_primality 4874540587086777007 (5 : ZMod 4874540587086777007)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (199, 1), (272887, 1), (204938549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (199, 1), (272887, 1), (204938549, 1)] : List FactorBlock).map factorBlockValue).prod) = 4874540587086777007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_73
      · exact prime_twentyTwoT_199
      · exact prime_twentyTwoT_272887
      · exact prime_twentyTwoT_204938549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4874540587086777007) ^ 2437270293543388503 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 4874540587086777007) ^ 1624846862362259002 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 4874540587086777007) ^ 66774528590229822 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 4874540587086777007) ^ 24495178829581794 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 4874540587086777007) ^ 17862853807938 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 4874540587086777007) ^ 23785376694 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_439
      · exact prime_twentyTwoT_853
      · exact prime_twentyTwoT_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_14121180779525611873 : Nat.Prime 14121180779525611873 := by
  apply lucas_primality 14121180779525611873 (5 : ZMod 14121180779525611873)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod) = 14121180779525611873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_23
      · exact prime_twentyTwoT_6395462309567759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14121180779525611873) ^ 7060590389762805936 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 4707060259841870624 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 613964381718504864 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 2208 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_21609402770898839089 : Nat.Prime 21609402770898839089 := by
  apply lucas_primality 21609402770898839089 (22 : ZMod 21609402770898839089)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (41, 1), (1009, 1), (706841, 1), (5131963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (41, 1), (1009, 1), (706841, 1), (5131963, 1)] : List FactorBlock).map factorBlockValue).prod) = 21609402770898839089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_41
      · exact prime_twentyTwoT_1009
      · exact prime_twentyTwoT_706841
      · exact prime_twentyTwoT_5131963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 21609402770898839089) ^ 10804701385449419544 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (22 : ZMod 21609402770898839089) ^ 7203134256966279696 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (22 : ZMod 21609402770898839089) ^ 527058604168264368 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (22 : ZMod 21609402770898839089) ^ 21416652894845232 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (22 : ZMod 21609402770898839089) ^ 30571801537968 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (22 : ZMod 21609402770898839089) ^ 4210747967376 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_28418646871883318789 : Nat.Prime 28418646871883318789 := by
  apply lucas_primality 28418646871883318789 (2 : ZMod 28418646871883318789)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (233, 1), (30492110377557209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (233, 1), (30492110377557209, 1)] : List FactorBlock).map factorBlockValue).prod) = 28418646871883318789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_233
      · exact prime_twentyTwoT_30492110377557209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 28418646871883318789) ^ 14209323435941659394 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28418646871883318789) ^ 121968441510228836 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28418646871883318789) ^ 932 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_37134887616756554077 : Nat.Prime 37134887616756554077 := by
  apply lucas_primality 37134887616756554077 (6 : ZMod 37134887616756554077)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (776813, 1), (1327893142907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (776813, 1), (1327893142907, 1)] : List FactorBlock).map factorBlockValue).prod) = 37134887616756554077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_776813
      · exact prime_twentyTwoT_1327893142907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 37134887616756554077) ^ 18567443808378277038 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 37134887616756554077) ^ 12378295872252184692 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 37134887616756554077) ^ 47804153144652 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 37134887616756554077) ^ 27965268 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_57709978139285874797 : Nat.Prime 57709978139285874797 := by
  apply lucas_primality 57709978139285874797 (2 : ZMod 57709978139285874797)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (55379759, 1), (260519272661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (55379759, 1), (260519272661, 1)] : List FactorBlock).map factorBlockValue).prod) = 57709978139285874797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_55379759
      · exact prime_twentyTwoT_260519272661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 57709978139285874797) ^ 28854989069642937398 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 57709978139285874797) ^ 1042077090644 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 57709978139285874797) ^ 221519036 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_110104639971994633747 : Nat.Prime 110104639971994633747 := by
  apply lucas_primality 110104639971994633747 (5 : ZMod 110104639971994633747)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (797, 1), (2093164517926973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (797, 1), (2093164517926973, 1)] : List FactorBlock).map factorBlockValue).prod) = 110104639971994633747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_797
      · exact prime_twentyTwoT_2093164517926973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 110104639971994633747) ^ 55052319985997316873 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 110104639971994633747) ^ 36701546657331544582 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 110104639971994633747) ^ 10009512724726784886 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 110104639971994633747) ^ 138148858183180218 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 110104639971994633747) ^ 52602 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_110910068172641332811 : Nat.Prime 110910068172641332811 := by
  apply lucas_primality 110910068172641332811 (2 : ZMod 110910068172641332811)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79, 1), (140392491357773839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79, 1), (140392491357773839, 1)] : List FactorBlock).map factorBlockValue).prod) = 110910068172641332811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_79
      · exact prime_twentyTwoT_140392491357773839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 110910068172641332811) ^ 55455034086320666405 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 110910068172641332811) ^ 22182013634528266562 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 110910068172641332811) ^ 1403924913577738390 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 110910068172641332811) ^ 790 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_145849035197483064341 : Nat.Prime 145849035197483064341 := by
  apply lucas_primality 145849035197483064341 (3 : ZMod 145849035197483064341)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (199, 1), (757, 1), (299969, 1), (161379451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (199, 1), (757, 1), (299969, 1), (161379451, 1)] : List FactorBlock).map factorBlockValue).prod) = 145849035197483064341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_199
      · exact prime_twentyTwoT_757
      · exact prime_twentyTwoT_299969
      · exact prime_twentyTwoT_161379451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 145849035197483064341) ^ 72924517598741532170 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 145849035197483064341) ^ 29169807039496612868 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 145849035197483064341) ^ 732909724610467660 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 145849035197483064341) ^ 192667153497335620 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 145849035197483064341) ^ 486213692739860 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 145849035197483064341) ^ 903764601340 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_282723354051033066407 : Nat.Prime 282723354051033066407 := by
  apply lucas_primality 282723354051033066407 (5 : ZMod 282723354051033066407)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (4874540587086777007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (4874540587086777007, 1)] : List FactorBlock).map factorBlockValue).prod) = 282723354051033066407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_29
      · exact prime_twentyTwoT_4874540587086777007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 282723354051033066407) ^ 141361677025516533203 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 282723354051033066407) ^ 9749081174173554014 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 282723354051033066407) ^ 58 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_452811813357361491437 : Nat.Prime 452811813357361491437 := by
  apply lucas_primality 452811813357361491437 (2 : ZMod 452811813357361491437)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (97, 1), (55733, 1), (130073, 1), (12383491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (97, 1), (55733, 1), (130073, 1), (12383491, 1)] : List FactorBlock).map factorBlockValue).prod) = 452811813357361491437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_97
      · exact prime_twentyTwoT_55733
      · exact prime_twentyTwoT_130073
      · exact prime_twentyTwoT_12383491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 452811813357361491437) ^ 226405906678680745718 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 452811813357361491437) ^ 34831677950566268572 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 452811813357361491437) ^ 4668163024302695788 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 452811813357361491437) ^ 8124662468508092 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 452811813357361491437) ^ 3481212960086732 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 452811813357361491437) ^ 36565764319396 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_558234740355005780371 : Nat.Prime 558234740355005780371 := by
  apply lucas_primality 558234740355005780371 (2 : ZMod 558234740355005780371)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (5426387, 1), (1143045681439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (5426387, 1), (1143045681439, 1)] : List FactorBlock).map factorBlockValue).prod) = 558234740355005780371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_5426387
      · exact prime_twentyTwoT_1143045681439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 558234740355005780371) ^ 279117370177502890185 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 558234740355005780371) ^ 186078246785001926790 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 558234740355005780371) ^ 111646948071001156074 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 558234740355005780371) ^ 102874111329510 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 558234740355005780371) ^ 488374830 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1113419261968560235841 : Nat.Prime 1113419261968560235841 := by
  apply lucas_primality 1113419261968560235841 (6 : ZMod 1113419261968560235841)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (130021, 1), (2502833, 1), (10692109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (130021, 1), (2502833, 1), (10692109, 1)] : List FactorBlock).map factorBlockValue).prod) = 1113419261968560235841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_130021
      · exact prime_twentyTwoT_2502833
      · exact prime_twentyTwoT_10692109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1113419261968560235841) ^ 556709630984280117920 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1113419261968560235841) ^ 222683852393712047168 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1113419261968560235841) ^ 8563380238335040 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1113419261968560235841) ^ 444863585372480 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1113419261968560235841) ^ 104134671837760 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1213214327206691504111 : Nat.Prime 1213214327206691504111 := by
  apply lucas_primality 1213214327206691504111 (17 : ZMod 1213214327206691504111)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (47, 1), (373297, 1), (531914489033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (47, 1), (373297, 1), (531914489033, 1)] : List FactorBlock).map factorBlockValue).prod) = 1213214327206691504111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_47
      · exact prime_twentyTwoT_373297
      · exact prime_twentyTwoT_531914489033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1213214327206691504111) ^ 606607163603345752055 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (17 : ZMod 1213214327206691504111) ^ 242642865441338300822 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (17 : ZMod 1213214327206691504111) ^ 93324179015899346470 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (17 : ZMod 1213214327206691504111) ^ 25813070791631734130 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (17 : ZMod 1213214327206691504111) ^ 3249997527991630 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (17 : ZMod 1213214327206691504111) ^ 2280844670 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_107
      · exact prime_twentyTwoT_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2853827719489851348443 : Nat.Prime 2853827719489851348443 := by
  apply lucas_primality 2853827719489851348443 (2 : ZMod 2853827719489851348443)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (59159, 1), (2192725397572529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (59159, 1), (2192725397572529, 1)] : List FactorBlock).map factorBlockValue).prod) = 2853827719489851348443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_59159
      · exact prime_twentyTwoT_2192725397572529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2853827719489851348443) ^ 1426913859744925674221 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2853827719489851348443) ^ 259438883589986486222 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2853827719489851348443) ^ 48239958746595638 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2853827719489851348443) ^ 1301498 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_3349408442130034682227 : Nat.Prime 3349408442130034682227 := by
  apply lucas_primality 3349408442130034682227 (2 : ZMod 3349408442130034682227)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (558234740355005780371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (558234740355005780371, 1)] : List FactorBlock).map factorBlockValue).prod) = 3349408442130034682227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_558234740355005780371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3349408442130034682227) ^ 1674704221065017341113 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3349408442130034682227) ^ 1116469480710011560742 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3349408442130034682227) ^ 6 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_3463701263446490329787 : Nat.Prime 3463701263446490329787 := by
  apply lucas_primality 3463701263446490329787 (2 : ZMod 3463701263446490329787)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (89, 1), (467, 1), (621911721757133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (89, 1), (467, 1), (621911721757133, 1)] : List FactorBlock).map factorBlockValue).prod) = 3463701263446490329787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_67
      · exact prime_twentyTwoT_89
      · exact prime_twentyTwoT_467
      · exact prime_twentyTwoT_621911721757133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3463701263446490329787) ^ 1731850631723245164893 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 51697033782783437758 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 38917991724117868874 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 7416919193675568158 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 5569442 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_4430773372276762682321 : Nat.Prime 4430773372276762682321 := by
  apply lucas_primality 4430773372276762682321 (3 : ZMod 4430773372276762682321)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (67, 1), (826636823185963187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (67, 1), (826636823185963187, 1)] : List FactorBlock).map factorBlockValue).prod) = 4430773372276762682321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_67
      · exact prime_twentyTwoT_826636823185963187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4430773372276762682321) ^ 2215386686138381341160 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4430773372276762682321) ^ 886154674455352536464 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4430773372276762682321) ^ 66130945854877054960 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 4430773372276762682321) ^ 5360 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_9109483663880487566509 : Nat.Prime 9109483663880487566509 := by
  apply lucas_primality 9109483663880487566509 (2 : ZMod 9109483663880487566509)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (179, 1), (11933, 1), (565567, 1), (628384961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (179, 1), (11933, 1), (565567, 1), (628384961, 1)] : List FactorBlock).map factorBlockValue).prod) = 9109483663880487566509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_179
      · exact prime_twentyTwoT_11933
      · exact prime_twentyTwoT_565567
      · exact prime_twentyTwoT_628384961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9109483663880487566509) ^ 4554741831940243783254 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 9109483663880487566509) ^ 3036494554626829188836 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 9109483663880487566509) ^ 50890970189276466852 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 9109483663880487566509) ^ 763385876466981276 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 9109483663880487566509) ^ 16106816104688724 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 9109483663880487566509) ^ 14496660851628 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_29
      · exact prime_twentyTwoT_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_19141499469217865992099 : Nat.Prime 19141499469217865992099 := by
  apply lucas_primality 19141499469217865992099 (7 : ZMod 19141499469217865992099)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (17, 1), (2437165707819947287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (17, 1), (2437165707819947287, 1)] : List FactorBlock).map factorBlockValue).prod) = 19141499469217865992099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_17
      · exact prime_twentyTwoT_2437165707819947287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 19141499469217865992099) ^ 9570749734608932996049 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 19141499469217865992099) ^ 6380499823072621997366 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 19141499469217865992099) ^ 2734499924173980856014 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 19141499469217865992099) ^ 1740136315383442362918 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 19141499469217865992099) ^ 1125970557012815646594 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (7 : ZMod 19141499469217865992099) ^ 7854 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_22442462496710053242007 : Nat.Prime 22442462496710053242007 := by
  apply lucas_primality 22442462496710053242007 (5 : ZMod 22442462496710053242007)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (2753, 1), (46850588275089773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (2753, 1), (46850588275089773, 1)] : List FactorBlock).map factorBlockValue).prod) = 22442462496710053242007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_29
      · exact prime_twentyTwoT_2753
      · exact prime_twentyTwoT_46850588275089773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 22442462496710053242007) ^ 11221231248355026621003 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 22442462496710053242007) ^ 7480820832236684414002 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 22442462496710053242007) ^ 773878017127932870414 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 22442462496710053242007) ^ 8152002359865620502 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 22442462496710053242007) ^ 479022 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_33440436836683723240447 : Nat.Prime 33440436836683723240447 := by
  apply lucas_primality 33440436836683723240447 (3 : ZMod 33440436836683723240447)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (151, 1), (2953667, 1), (961255552021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (151, 1), (2953667, 1), (961255552021, 1)] : List FactorBlock).map factorBlockValue).prod) = 33440436836683723240447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_151
      · exact prime_twentyTwoT_2953667
      · exact prime_twentyTwoT_961255552021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33440436836683723240447) ^ 16720218418341861620223 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 33440436836683723240447) ^ 11146812278894574413482 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 33440436836683723240447) ^ 2572341295129517172342 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 33440436836683723240447) ^ 221459846600554458546 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 33440436836683723240447) ^ 11321667891703338 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 33440436836683723240447) ^ 34788289926 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_36097547755948408265491 : Nat.Prime 36097547755948408265491 := by
  apply lucas_primality 36097547755948408265491 (3 : ZMod 36097547755948408265491)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (29131, 1), (727781, 1), (18918168251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (29131, 1), (727781, 1), (18918168251, 1)] : List FactorBlock).map factorBlockValue).prod) = 36097547755948408265491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_29131
      · exact prime_twentyTwoT_727781
      · exact prime_twentyTwoT_18918168251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36097547755948408265491) ^ 18048773877974204132745 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 36097547755948408265491) ^ 12032515918649469421830 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 36097547755948408265491) ^ 7219509551189681653098 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 36097547755948408265491) ^ 1239145506709292790 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 36097547755948408265491) ^ 49599464338789290 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 36097547755948408265491) ^ 1908088947990 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_57110078409302094014171 : Nat.Prime 57110078409302094014171 := by
  apply lucas_primality 57110078409302094014171 (6 : ZMod 57110078409302094014171)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (21160721, 1), (269887204737977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (21160721, 1), (269887204737977, 1)] : List FactorBlock).map factorBlockValue).prod) = 57110078409302094014171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_21160721
      · exact prime_twentyTwoT_269887204737977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 57110078409302094014171) ^ 28555039204651047007085 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 57110078409302094014171) ^ 11422015681860418802834 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 57110078409302094014171) ^ 2698872047379770 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (6 : ZMod 57110078409302094014171) ^ 211607210 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_67024695540586320517363 : Nat.Prime 67024695540586320517363 := by
  apply lucas_primality 67024695540586320517363 (3 : ZMod 67024695540586320517363)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (47, 1), (1899647, 1), (2909674311721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (47, 1), (1899647, 1), (2909674311721, 1)] : List FactorBlock).map factorBlockValue).prod) = 67024695540586320517363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_43
      · exact prime_twentyTwoT_47
      · exact prime_twentyTwoT_1899647
      · exact prime_twentyTwoT_2909674311721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 67024695540586320517363) ^ 33512347770293160258681 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 22341565180195440172454 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 1558713849781077221334 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 1426057351927368521646 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 35282710703928846 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 23035119522 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_262688826330237036027733 : Nat.Prime 262688826330237036027733 := by
  apply lucas_primality 262688826330237036027733 (5 : ZMod 262688826330237036027733)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (19, 1), (269, 1), (611866157797460743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (19, 1), (269, 1), (611866157797460743, 1)] : List FactorBlock).map factorBlockValue).prod) = 262688826330237036027733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_269
      · exact prime_twentyTwoT_611866157797460743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 262688826330237036027733) ^ 131344413165118518013866 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 262688826330237036027733) ^ 87562942110079012009244 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 262688826330237036027733) ^ 37526975190033862289676 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 262688826330237036027733) ^ 13825727701591422948828 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 262688826330237036027733) ^ 976538387844747345828 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 262688826330237036027733) ^ 429324 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_614861506554349437030163 : Nat.Prime 614861506554349437030163 := by
  apply lucas_primality 614861506554349437030163 (3 : ZMod 614861506554349437030163)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29304298123, 1), (3496992739049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29304298123, 1), (3496992739049, 1)] : List FactorBlock).map factorBlockValue).prod) = 614861506554349437030163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_29304298123
      · exact prime_twentyTwoT_3496992739049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 614861506554349437030163) ^ 307430753277174718515081 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 614861506554349437030163) ^ 204953835518116479010054 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 614861506554349437030163) ^ 20981956434294 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 614861506554349437030163) ^ 175825788738 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_1190165253512496105301087 : Nat.Prime 1190165253512496105301087 := by
  apply lucas_primality 1190165253512496105301087 (3 : ZMod 1190165253512496105301087)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (641, 1), (28351, 1), (42143426280649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (641, 1), (28351, 1), (42143426280649, 1)] : List FactorBlock).map factorBlockValue).prod) = 1190165253512496105301087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_37
      · exact prime_twentyTwoT_641
      · exact prime_twentyTwoT_28351
      · exact prime_twentyTwoT_42143426280649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1190165253512496105301087) ^ 595082626756248052650543 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1190165253512496105301087) ^ 396721751170832035100362 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1190165253512496105301087) ^ 170023607644642300757298 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1190165253512496105301087) ^ 32166628473310705548678 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1190165253512496105301087) ^ 1856732064762084407646 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1190165253512496105301087) ^ 41979656926122397986 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1190165253512496105301087) ^ 28240828014 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_2554495330019847759305633 : Nat.Prime 2554495330019847759305633 := by
  apply lucas_primality 2554495330019847759305633 (3 : ZMod 2554495330019847759305633)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (53, 2), (28418646871883318789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (53, 2), (28418646871883318789, 1)] : List FactorBlock).map factorBlockValue).prod) = 2554495330019847759305633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_53
      · exact prime_twentyTwoT_28418646871883318789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2554495330019847759305633) ^ 1277247665009923879652816 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554495330019847759305633) ^ 48198025094714108666144 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554495330019847759305633) ^ 89888 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_3176584202523459927363209 : Nat.Prime 3176584202523459927363209 := by
  apply lucas_primality 3176584202523459927363209 (3 : ZMod 3176584202523459927363209)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (36097547755948408265491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (36097547755948408265491, 1)] : List FactorBlock).map factorBlockValue).prod) = 3176584202523459927363209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_36097547755948408265491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3176584202523459927363209) ^ 1588292101261729963681604 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3176584202523459927363209) ^ 288780382047587266123928 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3176584202523459927363209) ^ 88 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_3229034320330489122936059 : Nat.Prime 3229034320330489122936059 := by
  apply lucas_primality 3229034320330489122936059 (2 : ZMod 3229034320330489122936059)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (358993, 1), (4497349976643679853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (358993, 1), (4497349976643679853, 1)] : List FactorBlock).map factorBlockValue).prod) = 3229034320330489122936059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_358993
      · exact prime_twentyTwoT_4497349976643679853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3229034320330489122936059) ^ 1614517160165244561468029 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3229034320330489122936059) ^ 8994699953287359706 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3229034320330489122936059) ^ 717986 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_3554717978715606107045231 : Nat.Prime 3554717978715606107045231 := by
  apply lucas_primality 3554717978715606107045231 (19 : ZMod 3554717978715606107045231)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (293, 1), (1213214327206691504111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (293, 1), (1213214327206691504111, 1)] : List FactorBlock).map factorBlockValue).prod) = 3554717978715606107045231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_293
      · exact prime_twentyTwoT_1213214327206691504111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 3554717978715606107045231) ^ 1777358989357803053522615 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (19 : ZMod 3554717978715606107045231) ^ 710943595743121221409046 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (19 : ZMod 3554717978715606107045231) ^ 12132143272066915041110 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (19 : ZMod 3554717978715606107045231) ^ 2930 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_3994758324414389477077247 : Nat.Prime 3994758324414389477077247 := by
  apply lucas_primality 3994758324414389477077247 (5 : ZMod 3994758324414389477077247)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (22442462496710053242007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (22442462496710053242007, 1)] : List FactorBlock).map factorBlockValue).prod) = 3994758324414389477077247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_89
      · exact prime_twentyTwoT_22442462496710053242007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3994758324414389477077247) ^ 1997379162207194738538623 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 3994758324414389477077247) ^ 44884924993420106484014 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (5 : ZMod 3994758324414389477077247) ^ 178 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_5698920124947872455138027 : Nat.Prime 5698920124947872455138027 := by
  apply lucas_primality 5698920124947872455138027 (2 : ZMod 5698920124947872455138027)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (89, 1), (1217, 1), (974357259695558663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (89, 1), (1217, 1), (974357259695558663, 1)] : List FactorBlock).map factorBlockValue).prod) = 5698920124947872455138027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_89
      · exact prime_twentyTwoT_1217
      · exact prime_twentyTwoT_974357259695558663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5698920124947872455138027) ^ 2849460062473936227569013 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698920124947872455138027) ^ 1899640041649290818379342 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698920124947872455138027) ^ 64032810392672724215034 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698920124947872455138027) ^ 4682760990096854934378 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698920124947872455138027) ^ 5848902 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_8442022541467734464540719 : Nat.Prime 8442022541467734464540719 := by
  apply lucas_primality 8442022541467734464540719 (3 : ZMod 8442022541467734464540719)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37889, 1), (37134887616756554077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37889, 1), (37134887616756554077, 1)] : List FactorBlock).map factorBlockValue).prod) = 8442022541467734464540719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_37889
      · exact prime_twentyTwoT_37134887616756554077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8442022541467734464540719) ^ 4221011270733867232270359 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8442022541467734464540719) ^ 2814007513822578154846906 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8442022541467734464540719) ^ 222809325700539324462 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8442022541467734464540719) ^ 227334 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_160554762038654875834876267 : Nat.Prime 160554762038654875834876267 := by
  apply lucas_primality 160554762038654875834876267 (2 : ZMod 160554762038654875834876267)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (137, 1), (36973, 1), (1304698691, 1), (4049080921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (137, 1), (36973, 1), (1304698691, 1), (4049080921, 1)] : List FactorBlock).map factorBlockValue).prod) = 160554762038654875834876267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_137
      · exact prime_twentyTwoT_36973
      · exact prime_twentyTwoT_1304698691
      · exact prime_twentyTwoT_4049080921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 160554762038654875834876267) ^ 80277381019327437917438133 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 160554762038654875834876267) ^ 53518254012884958611625422 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 160554762038654875834876267) ^ 1171932569625218071787418 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 160554762038654875834876267) ^ 4342486734607818565842 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 160554762038654875834876267) ^ 123058881829333326 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (2 : ZMod 160554762038654875834876267) ^ 39652149505325946 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_351484749327866079530404801 : Nat.Prime 351484749327866079530404801 := by
  apply lucas_primality 351484749327866079530404801 (89 : ZMod 351484749327866079530404801)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 351484749327866079530404801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_17
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_23
      · exact prime_twentyTwoT_29
      · exact prime_twentyTwoT_31
      · exact prime_twentyTwoT_41
      · exact prime_twentyTwoT_43
      · exact prime_twentyTwoT_47
      · exact prime_twentyTwoT_53
      · exact prime_twentyTwoT_59
      · exact prime_twentyTwoT_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (89 : ZMod 351484749327866079530404801) ^ 175742374663933039765202400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (89 : ZMod 351484749327866079530404801) ^ 117161583109288693176801600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (89 : ZMod 351484749327866079530404801) ^ 70296949865573215906080960 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (89 : ZMod 351484749327866079530404801) ^ 50212107046838011361486400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (89 : ZMod 351484749327866079530404801) ^ 31953159029806007230036800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (89 : ZMod 351484749327866079530404801) ^ 27037288409835852271569600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (89 : ZMod 351484749327866079530404801) ^ 20675573489874475266494400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (89 : ZMod 351484749327866079530404801) ^ 18499197333045583133179200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (89 : ZMod 351484749327866079530404801) ^ 15281945622950699110017600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (89 : ZMod 351484749327866079530404801) ^ 12120163769926416535531200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (89 : ZMod 351484749327866079530404801) ^ 11338217720253744500980800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (89 : ZMod 351484749327866079530404801) ^ 8572798764094294622692800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (89 : ZMod 351484749327866079530404801) ^ 8174063937857350686753600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (89 : ZMod 351484749327866079530404801) ^ 7478398921869491053838400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (89 : ZMod 351484749327866079530404801) ^ 6631787723167284519441600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (89 : ZMod 351484749327866079530404801) ^ 5957368632675696263227200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (89 : ZMod 351484749327866079530404801) ^ 5762045070948624254596800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_376954658699450578047100801 : Nat.Prime 376954658699450578047100801 := by
  apply lucas_primality 376954658699450578047100801 (23 : ZMod 376954658699450578047100801)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 376954658699450578047100801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_17
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_29
      · exact prime_twentyTwoT_31
      · exact prime_twentyTwoT_37
      · exact prime_twentyTwoT_41
      · exact prime_twentyTwoT_43
      · exact prime_twentyTwoT_47
      · exact prime_twentyTwoT_53
      · exact prime_twentyTwoT_59
      · exact prime_twentyTwoT_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 376954658699450578047100801) ^ 188477329349725289023550400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (23 : ZMod 376954658699450578047100801) ^ 125651552899816859349033600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (23 : ZMod 376954658699450578047100801) ^ 75390931739890115609420160 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (23 : ZMod 376954658699450578047100801) ^ 53850665528492939721014400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (23 : ZMod 376954658699450578047100801) ^ 34268605336313688913372800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (23 : ZMod 376954658699450578047100801) ^ 28996512207650044465161600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (23 : ZMod 376954658699450578047100801) ^ 22173803452908857532182400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (23 : ZMod 376954658699450578047100801) ^ 19839718878918451476163200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (23 : ZMod 376954658699450578047100801) ^ 12998436506877606139555200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (23 : ZMod 376954658699450578047100801) ^ 12159827699982276711196800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (23 : ZMod 376954658699450578047100801) ^ 10187963748633799406678400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (23 : ZMod 376954658699450578047100801) ^ 9194016065840258001148800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (23 : ZMod 376954658699450578047100801) ^ 8766387411615129722025600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (23 : ZMod 376954658699450578047100801) ^ 8020311887222352724406400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (23 : ZMod 376954658699450578047100801) ^ 7112352050933029774473600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (23 : ZMod 376954658699450578047100801) ^ 6389062011855094543171200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (23 : ZMod 376954658699450578047100801) ^ 6179584568843452099132800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_17
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_23
      · exact prime_twentyTwoT_29
      · exact prime_twentyTwoT_31
      · exact prime_twentyTwoT_37
      · exact prime_twentyTwoT_41
      · exact prime_twentyTwoT_43
      · exact prime_twentyTwoT_47
      · exact prime_twentyTwoT_53
      · exact prime_twentyTwoT_59
      · exact prime_twentyTwoT_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_406404241410345154457030551 : Nat.Prime 406404241410345154457030551 := by
  apply lucas_primality 406404241410345154457030551 (3 : ZMod 406404241410345154457030551)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 406404241410345154457030551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_17
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_23
      · exact prime_twentyTwoT_29
      · exact prime_twentyTwoT_31
      · exact prime_twentyTwoT_37
      · exact prime_twentyTwoT_41
      · exact prime_twentyTwoT_43
      · exact prime_twentyTwoT_47
      · exact prime_twentyTwoT_53
      · exact prime_twentyTwoT_59
      · exact prime_twentyTwoT_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 406404241410345154457030551) ^ 203202120705172577228515275 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 135468080470115051485676850 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 81280848282069030891406110 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 58057748772906450636718650 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 36945840128213195859730050 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 31261864723872704189002350 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 23906131847667362026884150 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 21389696916333955497738450 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 17669749626536745845957850 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 14013939358977419119207950 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 13109814239043392079259050 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 10983898416495814985325150 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 9912298570984028157488550 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 9451261428147561731558850 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 8646898753411599031000650 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 7668004554912172725604350 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 6888207481531273804356450 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 6662364613284346794377550 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_426391335250198194840163201 : Nat.Prime 426391335250198194840163201 := by
  apply lucas_primality 426391335250198194840163201 (67 : ZMod 426391335250198194840163201)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) = 426391335250198194840163201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_7
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_17
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_23
      · exact prime_twentyTwoT_29
      · exact prime_twentyTwoT_31
      · exact prime_twentyTwoT_37
      · exact prime_twentyTwoT_41
      · exact prime_twentyTwoT_43
      · exact prime_twentyTwoT_47
      · exact prime_twentyTwoT_53
      · exact prime_twentyTwoT_59
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 426391335250198194840163201) ^ 213195667625099097420081600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (67 : ZMod 426391335250198194840163201) ^ 142130445083399398280054400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (67 : ZMod 426391335250198194840163201) ^ 85278267050039638968032640 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (67 : ZMod 426391335250198194840163201) ^ 60913047892885456405737600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (67 : ZMod 426391335250198194840163201) ^ 38762848659108926803651200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (67 : ZMod 426391335250198194840163201) ^ 32799333480784476526166400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (67 : ZMod 426391335250198194840163201) ^ 25081843250011658520009600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (67 : ZMod 426391335250198194840163201) ^ 22441649223694641833692800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (67 : ZMod 426391335250198194840163201) ^ 18538753706530356297398400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (67 : ZMod 426391335250198194840163201) ^ 14703149491386144649660800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (67 : ZMod 426391335250198194840163201) ^ 13754559201619296607747200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (67 : ZMod 426391335250198194840163201) ^ 11524090141897248509193600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (67 : ZMod 426391335250198194840163201) ^ 10399788664638980361955200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (67 : ZMod 426391335250198194840163201) ^ 9916077563958097554422400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (67 : ZMod 426391335250198194840163201) ^ 9072156069153153081705600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (67 : ZMod 426391335250198194840163201) ^ 8045119533022607449814400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (67 : ZMod 426391335250198194840163201) ^ 7226971783901664319324800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem prime_twentyTwoT_530813703066573262964284801 : Nat.Prime 530813703066573262964284801 := by
  apply lucas_primality 530813703066573262964284801 (103 : ZMod 530813703066573262964284801)
  · rw [← twentyTwoTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 530813703066573262964284801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyTwoT_2
      · exact prime_twentyTwoT_3
      · exact prime_twentyTwoT_5
      · exact prime_twentyTwoT_11
      · exact prime_twentyTwoT_13
      · exact prime_twentyTwoT_17
      · exact prime_twentyTwoT_19
      · exact prime_twentyTwoT_23
      · exact prime_twentyTwoT_29
      · exact prime_twentyTwoT_31
      · exact prime_twentyTwoT_37
      · exact prime_twentyTwoT_41
      · exact prime_twentyTwoT_43
      · exact prime_twentyTwoT_47
      · exact prime_twentyTwoT_53
      · exact prime_twentyTwoT_59
      · exact prime_twentyTwoT_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 530813703066573262964284801) ^ 265406851533286631482142400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 176937901022191087654761600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 106162740613314652592856960 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 48255791187870296633116800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 40831823312813327920329600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 31224335474504309586134400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 27937563319293329629699200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 23078856655068402737577600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 18303920795399078033251200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 17123022679566879450460800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 14346316299096574674710400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 12946675684550567389372800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 12344504722478447975913600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 11293908575884537509878400 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 10015352888048552131401600 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 8996842424857173948547200 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide
    · change (103 : ZMod 530813703066573262964284801) ^ 8701863984697922343676800 ≠ 1
      rw [← twentyTwoTFastPow_eq_pow]
      decide

private theorem phi_twentyTwoT_26009871450262089885249955200 : Nat.totient 26009871450262089885249955200 = 3422570106105934066483200000 := by
  rw [← show ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955200 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_3, prime_twentyTwoT_5, prime_twentyTwoT_7, prime_twentyTwoT_11, prime_twentyTwoT_13, prime_twentyTwoT_17, prime_twentyTwoT_19, prime_twentyTwoT_23, prime_twentyTwoT_29, prime_twentyTwoT_31, prime_twentyTwoT_37, prime_twentyTwoT_41, prime_twentyTwoT_43, prime_twentyTwoT_47, prime_twentyTwoT_53, prime_twentyTwoT_59, prime_twentyTwoT_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955201 : Nat.totient 26009871450262089885249955201 = 26009424537446711085114733728 := by
  rw [← show ((([(58199, 1), (224916175177, 1), (1987018880687, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_58199, prime_twentyTwoT_224916175177, prime_twentyTwoT_1987018880687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955202 : Nat.totient 26009871450262089885249955202 = 12848235399057265116828962560 := by
  rw [← show ((([(2, 1), (83, 1), (895529, 1), (2064319931, 1), (84756586553, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_83, prime_twentyTwoT_895529, prime_twentyTwoT_2064319931, prime_twentyTwoT_84756586553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955203 : Nat.totient 26009871450262089885249955203 = 17145083756042899792873461504 := by
  rw [← show ((([(3, 1), (89, 1), (369688933, 1), (263505991609941173, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_3, prime_twentyTwoT_89, prime_twentyTwoT_369688933, prime_twentyTwoT_263505991609941173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955204 : Nat.totient 26009871450262089885249955204 = 13004934564712626979387822944 := by
  rw [← show ((([(2, 2), (11218483, 1), (15837208853, 1), (36598681199, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_11218483, prime_twentyTwoT_15837208853, prime_twentyTwoT_36598681199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955205 : Nat.totient 26009871450262089885249955205 = 20807585435853839134535784000 := by
  rw [← show ((([(5, 1), (66751, 1), (103039496123, 1), (756321939917, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_5, prime_twentyTwoT_66751, prime_twentyTwoT_103039496123, prime_twentyTwoT_756321939917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955206 : Nat.totient 26009871450262089885249955206 = 8664848159427323599564703744 := by
  rw [← show ((([(2, 1), (3, 1), (1697, 1), (2554495330019847759305633, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_3, prime_twentyTwoT_1697, prime_twentyTwoT_2554495330019847759305633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955207 : Nat.totient 26009871450262089885249955207 = 22293512605661595667472638080 := by
  rw [← show ((([(7, 1), (67121, 1), (67399, 1), (821350062669399719, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_7, prime_twentyTwoT_67121, prime_twentyTwoT_67399, prime_twentyTwoT_821350062669399719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955208 : Nat.totient 26009871450262089885249955208 = 13001847227232470590570714560 := by
  rw [← show ((([(2, 3), (4211, 1), (75111599, 1), (10279120799235109, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_4211, prime_twentyTwoT_75111599, prime_twentyTwoT_10279120799235109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955209 : Nat.totient 26009871450262089885249955209 = 17215166677116362258150379648 := by
  rw [← show ((([(3, 2), (139, 1), (451071857, 1), (46093020050440787, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_3, prime_twentyTwoT_139, prime_twentyTwoT_451071857, prime_twentyTwoT_46093020050440787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955210 : Nat.totient 26009871450262089885249955210 = 10378662057655325895374726400 := by
  rw [← show ((([(2, 1), (5, 1), (631, 1), (1181, 1), (3446959, 1), (1012564812501629, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_5, prime_twentyTwoT_631, prime_twentyTwoT_1181, prime_twentyTwoT_3446959, prime_twentyTwoT_1012564812501629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955211 : Nat.totient 26009871450262089885249955211 = 23645225188597186210076075520 := by
  rw [← show ((([(11, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_11, prime_twentyTwoT_210193, prime_twentyTwoT_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955212 : Nat.totient 26009871450262089885249955212 = 8669957148589855996409683968 := by
  rw [← show ((([(2, 2), (3, 1), (5789592673, 1), (374376818878815937, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_3, prime_twentyTwoT_5789592673, prime_twentyTwoT_374376818878815937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955213 : Nat.totient 26009871450262089885249955213 = 24009112097395452476355364848 := by
  rw [← show ((([(13, 1), (2278167139, 1), (878232026121702859, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_13, prime_twentyTwoT_2278167139, prime_twentyTwoT_878232026121702859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955214 : Nat.totient 26009871450262089885249955214 = 11146745103927582709685700600 := by
  rw [← show ((([(2, 1), (7, 1), (32531, 1), (57110078409302094014171, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_7, prime_twentyTwoT_32531, prime_twentyTwoT_57110078409302094014171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955215 : Nat.totient 26009871450262089885249955215 = 13854778830242677488074332160 := by
  rw [← show ((([(3, 1), (5, 1), (977, 1), (4691, 1), (6385035269, 1), (59254815407, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_3, prime_twentyTwoT_5, prime_twentyTwoT_977, prime_twentyTwoT_4691, prime_twentyTwoT_6385035269, prime_twentyTwoT_59254815407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955216 : Nat.totient 26009871450262089885249955216 = 12989365573029065613379666944 := by
  rw [← show ((([(2, 4), (857, 1), (32869, 1), (57709978139285874797, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_857, prime_twentyTwoT_32869, prime_twentyTwoT_57709978139285874797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955217 : Nat.totient 26009871450262089885249955217 = 24415962878820748483896127552 := by
  rw [← show ((([(17, 1), (383, 1), (3994758324414389477077247, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_17, prime_twentyTwoT_383, prime_twentyTwoT_3994758324414389477077247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955218 : Nat.totient 26009871450262089885249955218 = 8584115657778454378661222400 := by
  rw [← show ((([(2, 1), (3, 2), (101, 1), (25824109, 1), (554011756364663489, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_3, prime_twentyTwoT_101, prime_twentyTwoT_25824109, prime_twentyTwoT_554011756364663489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955219 : Nat.totient 26009871450262089885249955219 = 24279540703258704522081246720 := by
  rw [← show ((([(19, 1), (131, 1), (173, 1), (1103, 1), (4339, 1), (5639, 1), (2238205449829, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_19, prime_twentyTwoT_131, prime_twentyTwoT_173, prime_twentyTwoT_1103, prime_twentyTwoT_4339, prime_twentyTwoT_5639, prime_twentyTwoT_2238205449829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955220 : Nat.totient 26009871450262089885249955220 = 10257128243015157081441346560 := by
  rw [← show ((([(2, 2), (5, 1), (71, 1), (37967, 1), (834527, 1), (3072847, 1), (188131817, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_5, prime_twentyTwoT_71, prime_twentyTwoT_37967, prime_twentyTwoT_834527, prime_twentyTwoT_3072847, prime_twentyTwoT_188131817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955221 : Nat.totient 26009871450262089885249955221 = 14856036099828633646526056896 := by
  rw [← show ((([(3, 1), (7, 1), (2203, 1), (28231919, 1), (35140247, 1), (566707819, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_3, prime_twentyTwoT_7, prime_twentyTwoT_2203, prime_twentyTwoT_28231919, prime_twentyTwoT_35140247, prime_twentyTwoT_566707819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955222 : Nat.totient 26009871450262089885249955222 = 11705548278532956395009761920 := by
  rw [← show ((([(2, 1), (11, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_11, prime_twentyTwoT_103, prime_twentyTwoT_5009, prime_twentyTwoT_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955223 : Nat.totient 26009871450262089885249955223 = 24856004456030461516996496160 := by
  rw [← show ((([(23, 1), (1327, 1), (5843, 1), (145849035197483064341, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_23, prime_twentyTwoT_1327, prime_twentyTwoT_5843, prime_twentyTwoT_145849035197483064341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955224 : Nat.totient 26009871450262089885249955224 = 8629362319768747274732150784 := by
  rw [← show ((([(2, 3), (3, 1), (257, 1), (1259, 1), (3349408442130034682227, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_3, prime_twentyTwoT_257, prime_twentyTwoT_1259, prime_twentyTwoT_3349408442130034682227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955225 : Nat.totient 26009871450262089885249955225 = 20741403834572171111382528000 := by
  rw [← show ((([(5, 2), (313, 1), (2029241, 1), (4938853, 1), (331660790141, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_5, prime_twentyTwoT_313, prime_twentyTwoT_2029241, prime_twentyTwoT_4938853, prime_twentyTwoT_331660790141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955226 : Nat.totient 26009871450262089885249955226 = 11997177715888466215332520944 := by
  rw [← show ((([(2, 1), (13, 1), (1627, 1), (614861506554349437030163, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_13, prime_twentyTwoT_1627, prime_twentyTwoT_614861506554349437030163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955227 : Nat.totient 26009871450262089885249955227 = 17275929376557845680239817800 := by
  rw [← show ((([(3, 3), (271, 1), (3554717978715606107045231, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_3, prime_twentyTwoT_271, prime_twentyTwoT_3554717978715606107045231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955228 : Nat.totient 26009871450262089885249955228 = 11078700722898664052788322544 := by
  rw [← show ((([(2, 2), (7, 1), (163, 1), (5698920124947872455138027, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_7, prime_twentyTwoT_163, prime_twentyTwoT_5698920124947872455138027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955229 : Nat.totient 26009871450262089885249955229 = 24929672912791419929195351424 := by
  rw [← show ((([(29, 1), (137, 1), (2340867574039, 1), (2796680117807, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_29, prime_twentyTwoT_137, prime_twentyTwoT_2340867574039, prime_twentyTwoT_2796680117807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955230 : Nat.totient 26009871450262089885249955230 = 6934160660621173445213927424 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (4493, 1), (31159, 1), (222419, 1), (940573, 1), (29602789, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_3, prime_twentyTwoT_5, prime_twentyTwoT_4493, prime_twentyTwoT_31159, prime_twentyTwoT_222419, prime_twentyTwoT_940573, prime_twentyTwoT_29602789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955231 : Nat.totient 26009871450262089885249955231 = 24915617903694343493422540800 := by
  rw [← show ((([(31, 1), (109, 1), (1033, 1), (159671, 1), (24507097, 1), (1904284259, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_31, prime_twentyTwoT_109, prime_twentyTwoT_1033, prime_twentyTwoT_159671, prime_twentyTwoT_24507097, prime_twentyTwoT_1904284259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955232 : Nat.totient 26009871450262089885249955232 = 12740054128354647803940168960 := by
  rw [← show ((([(2, 5), (67, 1), (181, 1), (67024695540586320517363, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_67, prime_twentyTwoT_181, prime_twentyTwoT_67024695540586320517363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955233 : Nat.totient 26009871450262089885249955233 = 15715497292608989121442560000 := by
  rw [← show ((([(3, 1), (11, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_3, prime_twentyTwoT_11, prime_twentyTwoT_421, prime_twentyTwoT_1483, prime_twentyTwoT_2072201, prime_twentyTwoT_2567179, prime_twentyTwoT_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955234 : Nat.totient 26009871450262089885249955234 = 12239939492248792397892164352 := by
  rw [← show ((([(2, 1), (17, 1), (889731133, 1), (859806059102301397, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_17, prime_twentyTwoT_889731133, prime_twentyTwoT_859806059102301397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955235 : Nat.totient 26009871450262089885249955235 = 17772487628751068372478034560 := by
  rw [← show ((([(5, 1), (7, 1), (293, 1), (8971, 1), (282723354051033066407, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_5, prime_twentyTwoT_7, prime_twentyTwoT_293, prime_twentyTwoT_8971, prime_twentyTwoT_282723354051033066407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955236 : Nat.totient 26009871450262089885249955236 = 8669828541764306265069873600 := by
  rw [← show ((([(2, 2), (3, 2), (67901, 1), (9392503, 1), (1132865085569267, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_3, prime_twentyTwoT_67901, prime_twentyTwoT_9392503, prime_twentyTwoT_1132865085569267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955237 : Nat.totient 26009871450262089885249955237 = 25306861868512926857997926400 := by
  rw [← show ((([(37, 1), (631361, 1), (1113419261968560235841, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_37, prime_twentyTwoT_631361, prime_twentyTwoT_1113419261968560235841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955238 : Nat.totient 26009871450262089885249955238 = 12250202219670793464078336000 := by
  rw [← show ((([(2, 1), (19, 1), (241, 1), (641, 1), (4430773372276762682321, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_19, prime_twentyTwoT_241, prime_twentyTwoT_641, prime_twentyTwoT_4430773372276762682321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955239 : Nat.totient 26009871450262089885249955239 = 15803466197627598917620224096 := by
  rw [← show ((([(3, 1), (13, 1), (79, 1), (8442022541467734464540719, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_3, prime_twentyTwoT_13, prime_twentyTwoT_79, prime_twentyTwoT_8442022541467734464540719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955240 : Nat.totient 26009871450262089885249955240 = 10365263002105337358153246720 := by
  rw [← show ((([(2, 3), (5, 1), (269, 1), (1127981, 1), (2143009765547021929, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_5, prime_twentyTwoT_269, prime_twentyTwoT_1127981, prime_twentyTwoT_2143009765547021929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955241 : Nat.totient 26009871450262089885249955241 = 25375132250298557745027609600 := by
  rw [← show ((([(41, 1), (72073, 1), (2285686021, 1), (3850926034597, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_41, prime_twentyTwoT_72073, prime_twentyTwoT_2285686021, prime_twentyTwoT_3850926034597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955242 : Nat.totient 26009871450262089885249955242 = 7384058134333903213780155840 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (157, 1), (2848589311, 1), (1384711894151563, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_3, prime_twentyTwoT_7, prime_twentyTwoT_157, prime_twentyTwoT_2848589311, prime_twentyTwoT_1384711894151563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955243 : Nat.totient 26009871450262089885249955243 = 25404990718486881232535200200 := by
  rw [← show ((([(43, 1), (67971064771, 1), (8899091597863531, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_43, prime_twentyTwoT_67971064771, prime_twentyTwoT_8899091597863531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955244 : Nat.totient 26009871450262089885249955244 = 11822668831358244907644122000 := by
  rw [← show ((([(2, 2), (11, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_11, prime_twentyTwoT_1222615931, prime_twentyTwoT_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955245 : Nat.totient 26009871450262089885249955245 = 13794434616451849533182839776 := by
  rw [← show ((([(3, 2), (5, 1), (179, 1), (3229034320330489122936059, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_3, prime_twentyTwoT_5, prime_twentyTwoT_179, prime_twentyTwoT_3229034320330489122936059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955246 : Nat.totient 26009871450262089885249955246 = 12427888913613301365238510080 := by
  rw [← show ((([(2, 1), (23, 1), (1307, 1), (5927, 1), (289278289, 1), (252321361381, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_23, prime_twentyTwoT_1307, prime_twentyTwoT_5927, prime_twentyTwoT_289278289, prime_twentyTwoT_252321361381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955247 : Nat.totient 26009871450262089885249955247 = 25455283390226096470799008000 := by
  rw [← show ((([(47, 1), (26501, 1), (182279, 1), (294953, 1), (388408415123, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_47, prime_twentyTwoT_26501, prime_twentyTwoT_182279, prime_twentyTwoT_294953, prime_twentyTwoT_388408415123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955248 : Nat.totient 26009871450262089885249955248 = 8669955375526272532743822400 := by
  rw [← show ((([(2, 4), (3, 1), (4885691, 1), (110910068172641332811, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_3, prime_twentyTwoT_4885691, prime_twentyTwoT_110910068172641332811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955249 : Nat.totient 26009871450262089885249955249 = 22294175528796077044499961600 := by
  rw [← show ((([(7, 2), (530813703066573262964284801, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_7, prime_twentyTwoT_530813703066573262964284801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955250 : Nat.totient 26009871450262089885249955250 = 10403944713069279782454072000 := by
  rw [← show ((([(2, 1), (5, 3), (2719511, 1), (251922637, 1), (151858876903, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_5, prime_twentyTwoT_2719511, prime_twentyTwoT_251922637, prime_twentyTwoT_151858876903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955251 : Nat.totient 26009871450262089885249955251 = 16319919341324257787792793728 := by
  rw [← show ((([(3, 1), (17, 1), (981356944319, 1), (519686014726079, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_3, prime_twentyTwoT_17, prime_twentyTwoT_981356944319, prime_twentyTwoT_519686014726079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955252 : Nat.totient 26009871450262089885249955252 = 12003300760809558825227877120 := by
  rw [← show ((([(2, 2), (13, 1), (12227, 1), (43891, 1), (932050565158189193, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_13, prime_twentyTwoT_12227, prime_twentyTwoT_43891, prime_twentyTwoT_932050565158189193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955253 : Nat.totient 26009871450262089885249955253 = 25487238071867979573115023360 := by
  rw [← show ((([(53, 1), (947, 1), (5449, 1), (102953, 1), (3274511, 1), (282104549, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_53, prime_twentyTwoT_947, prime_twentyTwoT_5449, prime_twentyTwoT_102953, prime_twentyTwoT_3274511, prime_twentyTwoT_282104549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955254 : Nat.totient 26009871450262089885249955254 = 8669957150087363295083318364 := by
  rw [← show ((([(2, 1), (3, 4), (160554762038654875834876267, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_3, prime_twentyTwoT_160554762038654875834876267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955255 : Nat.totient 26009871450262089885249955255 = 18832753673753496183975381120 := by
  rw [← show ((([(5, 1), (11, 1), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_5, prime_twentyTwoT_11, prime_twentyTwoT_239, prime_twentyTwoT_4327, prime_twentyTwoT_1214459, prime_twentyTwoT_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955256 : Nat.totient 26009871450262089885249955256 = 11147087758113909098464053600 := by
  rw [← show ((([(2, 3), (7, 1), (1773847591, 1), (261838724217232711, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_7, prime_twentyTwoT_1773847591, prime_twentyTwoT_261838724217232711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955257 : Nat.totient 26009871450262089885249955257 = 16202255844828804556939943040 := by
  rw [← show ((([(3, 1), (19, 1), (73, 1), (294725971, 1), (21209092332463747, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_3, prime_twentyTwoT_19, prime_twentyTwoT_73, prime_twentyTwoT_294725971, prime_twentyTwoT_21209092332463747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955258 : Nat.totient 26009871450262089885249955258 = 12556455383309608475870760000 := by
  rw [← show ((([(2, 1), (29, 1), (432391, 1), (2395051, 1), (433030813401061, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_29, prime_twentyTwoT_432391, prime_twentyTwoT_2395051, prime_twentyTwoT_433030813401061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955259 : Nat.totient 26009871450262089885249955259 = 25567086626107560705822431976 := by
  rw [← show ((([(59, 1), (13183, 1), (33440436836683723240447, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_59, prime_twentyTwoT_13183, prime_twentyTwoT_33440436836683723240447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955260 : Nat.totient 26009871450262089885249955260 = 6884277218534635399817625600 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (149, 1), (2161, 1), (4457, 1), (16987, 1), (17782245395071, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_3, prime_twentyTwoT_5, prime_twentyTwoT_149, prime_twentyTwoT_2161, prime_twentyTwoT_4457, prime_twentyTwoT_16987, prime_twentyTwoT_17782245395071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955261 : Nat.totient 26009871450262089885249955261 = 25583480115011891690409792000 := by
  rw [← show ((([(61, 1), (426391335250198194840163201, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_61, prime_twentyTwoT_426391335250198194840163201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955262 : Nat.totient 26009871450262089885249955262 = 12577541004691749285007808160 := by
  rw [← show ((([(2, 1), (31, 1), (1597, 1), (262688826330237036027733, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955262 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_31, prime_twentyTwoT_1597, prime_twentyTwoT_262688826330237036027733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955263 : Nat.totient 26009871450262089885249955263 = 14764354654624923179653516800 := by
  rw [← show ((([(3, 2), (7, 1), (151, 1), (71487738337, 1), (38246275718023, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955263 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_3, prime_twentyTwoT_7, prime_twentyTwoT_151, prime_twentyTwoT_71487738337, prime_twentyTwoT_38246275718023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955264 : Nat.totient 26009871450262089885249955264 = 13004935725131044942624977600 := by
  rw [← show ((([(2, 6), (406404241410345154457030551, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955264 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_406404241410345154457030551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955265 : Nat.totient 26009871450262089885249955265 = 19137949289701069718594246400 := by
  rw [← show ((([(5, 1), (13, 2), (277, 1), (28920407891, 1), (3842353464491, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955265 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_5, prime_twentyTwoT_13, prime_twentyTwoT_277, prime_twentyTwoT_28920407891, prime_twentyTwoT_3842353464491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955266 : Nat.totient 26009871450262089885249955266 = 7881779227352148450075744000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955266 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_3, prime_twentyTwoT_11, prime_twentyTwoT_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955267 : Nat.totient 26009871450262089885249955267 = 25854123713774159805575217600 := by
  rw [← show ((([(167, 1), (7948202681, 1), (19595339913439021, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955267 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_167, prime_twentyTwoT_7948202681, prime_twentyTwoT_19595339913439021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955268 : Nat.totient 26009871450262089885249955268 = 12120714583812821536492884480 := by
  rw [← show ((([(2, 2), (17, 1), (199, 1), (211, 1), (9109483663880487566509, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955268 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_17, prime_twentyTwoT_199, prime_twentyTwoT_211, prime_twentyTwoT_9109483663880487566509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955269 : Nat.totient 26009871450262089885249955269 = 16586004982775825434072435200 := by
  rw [← show ((([(3, 1), (23, 1), (376954658699450578047100801, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955269 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_3, prime_twentyTwoT_23, prime_twentyTwoT_376954658699450578047100801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955270 : Nat.totient 26009871450262089885249955270 = 8895207556753302679280698752 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (397, 1), (946695979, 1), (988642159474447, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955270 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_5, prime_twentyTwoT_7, prime_twentyTwoT_397, prime_twentyTwoT_946695979, prime_twentyTwoT_988642159474447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955271 : Nat.totient 26009871450262089885249955271 = 25898241100665586308521788800 := by
  rw [← show ((([(233, 1), (1065061968151, 1), (104811131098537, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955271 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_233, prime_twentyTwoT_1065061968151, prime_twentyTwoT_104811131098537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955272 : Nat.totient 26009871450262089885249955272 = 8644230271161498522667640832 := by
  rw [← show ((([(2, 3), (3, 2), (337, 1), (2779889117, 1), (385610041946069, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955272 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_3, prime_twentyTwoT_337, prime_twentyTwoT_2779889117, prime_twentyTwoT_385610041946069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955273 : Nat.totient 26009871450262089885249955273 = 25665085046154267093132251136 := by
  rw [← show ((([(97, 1), (353, 1), (6899, 1), (110104639971994633747, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955273 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_97, prime_twentyTwoT_353, prime_twentyTwoT_6899, prime_twentyTwoT_110104639971994633747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955274 : Nat.totient 26009871450262089885249955274 = 12653450975803178863094572800 := by
  rw [← show ((([(2, 1), (37, 1), (351484749327866079530404801, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955274 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_37, prime_twentyTwoT_351484749327866079530404801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955275 : Nat.totient 26009871450262089885249955275 = 13867102910643709196836454400 := by
  rw [← show ((([(3, 1), (5, 2), (4721, 1), (11987, 1), (23447, 1), (97849, 1), (2671091477, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955275 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_3, prime_twentyTwoT_5, prime_twentyTwoT_4721, prime_twentyTwoT_11987, prime_twentyTwoT_23447, prime_twentyTwoT_97849, prime_twentyTwoT_2671091477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955276 : Nat.totient 26009871450262089885249955276 = 12210454279568422095594163200 := by
  rw [← show ((([(2, 2), (19, 1), (113, 1), (13163, 1), (455471, 1), (470579, 1), (1073490031, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955276 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_19, prime_twentyTwoT_113, prime_twentyTwoT_13163, prime_twentyTwoT_455471, prime_twentyTwoT_470579, prime_twentyTwoT_1073490031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955277 : Nat.totient 26009871450262089885249955277 = 20267224476829717796483417520 := by
  rw [← show ((([(7, 1), (11, 1), (97523, 1), (3463701263446490329787, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955277 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_7, prime_twentyTwoT_11, prime_twentyTwoT_97523, prime_twentyTwoT_3463701263446490329787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955278 : Nat.totient 26009871450262089885249955278 = 8002948118165992445902531200 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (89669, 1), (56990814479, 1), (65252388451, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955278 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_3, prime_twentyTwoT_13, prime_twentyTwoT_89669, prime_twentyTwoT_56990814479, prime_twentyTwoT_65252388451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955279 : Nat.totient 26009871450262089885249955279 = 26009852308762620667382604360 := by
  rw [← show ((([(1358821, 1), (19141499469217865992099, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955279 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_1358821, prime_twentyTwoT_19141499469217865992099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955280 : Nat.totient 26009871450262089885249955280 = 10403948566556731304205120000 := by
  rw [← show ((([(2, 4), (5, 1), (767926501, 1), (423378269541287941, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955280 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_5, prime_twentyTwoT_767926501, prime_twentyTwoT_423378269541287941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955281 : Nat.totient 26009871450262089885249955281 = 17177859015212178549589170960 := by
  rw [← show ((([(3, 3), (107, 1), (1543503319, 1), (5832880731578591, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955281 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_3, prime_twentyTwoT_107, prime_twentyTwoT_1543503319, prime_twentyTwoT_5832880731578591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955282 : Nat.totient 26009871450262089885249955282 = 12687742140935135493784356000 := by
  rw [← show ((([(2, 1), (41, 1), (423992911, 1), (748110513271031791, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955282 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_41, prime_twentyTwoT_423992911, prime_twentyTwoT_748110513271031791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955283 : Nat.totient 26009871450262089885249955283 = 25917963774872409019164094344 := by
  rw [← show ((([(283, 1), (10707451823, 1), (8583524305166887, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955283 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_283, prime_twentyTwoT_10707451823, prime_twentyTwoT_8583524305166887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955284 : Nat.totient 26009871450262089885249955284 = 7431391324306359179583952896 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (14329009, 1), (21609402770898839089, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955284 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_3, prime_twentyTwoT_7, prime_twentyTwoT_14329009, prime_twentyTwoT_21609402770898839089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955285 : Nat.totient 26009871450262089885249955285 = 19347951982706996093507232768 := by
  rw [← show ((([(5, 1), (17, 1), (83, 1), (33026989, 1), (111627758947967783, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955285 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_5, prime_twentyTwoT_17, prime_twentyTwoT_83, prime_twentyTwoT_33026989, prime_twentyTwoT_111627758947967783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955286 : Nat.totient 26009871450262089885249955286 = 12699771255421074380190890304 := by
  rw [← show ((([(2, 1), (43, 1), (4663, 1), (36966987433, 1), (1754527902319, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955286 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_43, prime_twentyTwoT_4663, prime_twentyTwoT_36966987433, prime_twentyTwoT_1754527902319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955287 : Nat.totient 26009871450262089885249955287 = 16732532259020039637856665600 := by
  rw [← show ((([(3, 1), (29, 1), (3041, 1), (4337, 1), (186871, 1), (121302904891543, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955287 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_3, prime_twentyTwoT_29, prime_twentyTwoT_3041, prime_twentyTwoT_4337, prime_twentyTwoT_186871, prime_twentyTwoT_121302904891543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955288 : Nat.totient 26009871450262089885249955288 = 11822668276180991493251911680 := by
  rw [← show ((([(2, 3), (11, 1), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955288 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_11, prime_twentyTwoT_20930737, prime_twentyTwoT_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955289 : Nat.totient 26009871450262089885249955289 = 26009870997450276527831023056 := by
  rw [← show ((([(57440797, 1), (452811813357361491437, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955289 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_57440797, prime_twentyTwoT_452811813357361491437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955290 : Nat.totient 26009871450262089885249955290 = 6935897228204622879631861728 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (101267, 1), (2853827719489851348443, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955290 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_3, prime_twentyTwoT_5, prime_twentyTwoT_101267, prime_twentyTwoT_2853827719489851348443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955291 : Nat.totient 26009871450262089885249955291 = 20288112032302005580895606400 := by
  rw [← show ((([(7, 1), (13, 1), (71, 1), (15991, 1), (2095699, 1), (120125147872859, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955291 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_7, prime_twentyTwoT_13, prime_twentyTwoT_71, prime_twentyTwoT_15991, prime_twentyTwoT_2095699, prime_twentyTwoT_120125147872859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955292 : Nat.totient 26009871450262089885249955292 = 12299734032170836838750341376 := by
  rw [← show ((([(2, 2), (23, 1), (89, 1), (3176584202523459927363209, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955292 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_23, prime_twentyTwoT_89, prime_twentyTwoT_3176584202523459927363209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955293 : Nat.totient 26009871450262089885249955293 = 16775857787861514719817216000 := by
  rw [← show ((([(3, 1), (31, 1), (3847, 1), (78401, 1), (147163, 1), (1674623, 1), (3762667, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955293 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_3, prime_twentyTwoT_31, prime_twentyTwoT_3847, prime_twentyTwoT_78401, prime_twentyTwoT_147163, prime_twentyTwoT_1674623, prime_twentyTwoT_3762667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955294 : Nat.totient 26009871450262089885249955294 = 12679838512242277911209115360 := by
  rw [← show ((([(2, 1), (47, 1), (263, 1), (103835981, 1), (10132269515533267, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955294 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_47, prime_twentyTwoT_263, prime_twentyTwoT_103835981, prime_twentyTwoT_10132269515533267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955295 : Nat.totient 26009871450262089885249955295 = 19712744669777316022900834560 := by
  rw [← show ((([(5, 1), (19, 2), (2370444491, 1), (6078986930589809, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955295 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_5, prime_twentyTwoT_19, prime_twentyTwoT_2370444491, prime_twentyTwoT_6078986930589809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955296 : Nat.totient 26009871450262089885249955296 = 8669168020951656354340571136 := by
  rw [← show ((([(2, 5), (3, 1), (10987, 1), (465392159, 1), (52986933480497, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955296 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_3, prime_twentyTwoT_10987, prime_twentyTwoT_465392159, prime_twentyTwoT_52986933480497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955297 : Nat.totient 26009871450262089885249955297 = 26009871450250390673687840916 := by
  rw [← show ((([(2223638394763, 1), (11696987923719619, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955297 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2223638394763, prime_twentyTwoT_11696987923719619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955298 : Nat.totient 26009871450262089885249955298 = 11097100823750513685827325864 := by
  rw [← show ((([(2, 1), (7, 2), (223, 1), (1190165253512496105301087, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955298 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_2, prime_twentyTwoT_7, prime_twentyTwoT_223, prime_twentyTwoT_1190165253512496105301087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyTwoT_26009871450262089885249955299 : Nat.totient 26009871450262089885249955299 = 15482048296470442263827712000 := by
  rw [← show ((([(3, 2), (11, 1), (67, 1), (491, 1), (1061, 1), (9492089, 1), (792993323477, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262089885249955299 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyTwoT_3, prime_twentyTwoT_11, prime_twentyTwoT_67, prime_twentyTwoT_491, prime_twentyTwoT_1061, prime_twentyTwoT_9492089, prime_twentyTwoT_792993323477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64TwentyTwoT : certifiedKill 1 26009871450262089885249955199 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_twentyTwoT_26009871450262089885249955200, phi_twentyTwoT_26009871450262089885249955201, phi_twentyTwoT_26009871450262089885249955202,
    phi_twentyTwoT_26009871450262089885249955203, phi_twentyTwoT_26009871450262089885249955204, phi_twentyTwoT_26009871450262089885249955205,
    phi_twentyTwoT_26009871450262089885249955206, phi_twentyTwoT_26009871450262089885249955207, phi_twentyTwoT_26009871450262089885249955208,
    phi_twentyTwoT_26009871450262089885249955209, phi_twentyTwoT_26009871450262089885249955210, phi_twentyTwoT_26009871450262089885249955211,
    phi_twentyTwoT_26009871450262089885249955212, phi_twentyTwoT_26009871450262089885249955213, phi_twentyTwoT_26009871450262089885249955214,
    phi_twentyTwoT_26009871450262089885249955215, phi_twentyTwoT_26009871450262089885249955216, phi_twentyTwoT_26009871450262089885249955217,
    phi_twentyTwoT_26009871450262089885249955218, phi_twentyTwoT_26009871450262089885249955219, phi_twentyTwoT_26009871450262089885249955220,
    phi_twentyTwoT_26009871450262089885249955221, phi_twentyTwoT_26009871450262089885249955222, phi_twentyTwoT_26009871450262089885249955223,
    phi_twentyTwoT_26009871450262089885249955224, phi_twentyTwoT_26009871450262089885249955225, phi_twentyTwoT_26009871450262089885249955226,
    phi_twentyTwoT_26009871450262089885249955227, phi_twentyTwoT_26009871450262089885249955228, phi_twentyTwoT_26009871450262089885249955229,
    phi_twentyTwoT_26009871450262089885249955230, phi_twentyTwoT_26009871450262089885249955231, phi_twentyTwoT_26009871450262089885249955232,
    phi_twentyTwoT_26009871450262089885249955233, phi_twentyTwoT_26009871450262089885249955234, phi_twentyTwoT_26009871450262089885249955235,
    phi_twentyTwoT_26009871450262089885249955236, phi_twentyTwoT_26009871450262089885249955237, phi_twentyTwoT_26009871450262089885249955238,
    phi_twentyTwoT_26009871450262089885249955239, phi_twentyTwoT_26009871450262089885249955240, phi_twentyTwoT_26009871450262089885249955241,
    phi_twentyTwoT_26009871450262089885249955242, phi_twentyTwoT_26009871450262089885249955243, phi_twentyTwoT_26009871450262089885249955244,
    phi_twentyTwoT_26009871450262089885249955245, phi_twentyTwoT_26009871450262089885249955246, phi_twentyTwoT_26009871450262089885249955247,
    phi_twentyTwoT_26009871450262089885249955248, phi_twentyTwoT_26009871450262089885249955249, phi_twentyTwoT_26009871450262089885249955250,
    phi_twentyTwoT_26009871450262089885249955251, phi_twentyTwoT_26009871450262089885249955252, phi_twentyTwoT_26009871450262089885249955253,
    phi_twentyTwoT_26009871450262089885249955254, phi_twentyTwoT_26009871450262089885249955255, phi_twentyTwoT_26009871450262089885249955256,
    phi_twentyTwoT_26009871450262089885249955257, phi_twentyTwoT_26009871450262089885249955258, phi_twentyTwoT_26009871450262089885249955259,
    phi_twentyTwoT_26009871450262089885249955260, phi_twentyTwoT_26009871450262089885249955261, phi_twentyTwoT_26009871450262089885249955262,
    phi_twentyTwoT_26009871450262089885249955263, phi_twentyTwoT_26009871450262089885249955264, phi_twentyTwoT_26009871450262089885249955265,
    phi_twentyTwoT_26009871450262089885249955266, phi_twentyTwoT_26009871450262089885249955267, phi_twentyTwoT_26009871450262089885249955268,
    phi_twentyTwoT_26009871450262089885249955269, phi_twentyTwoT_26009871450262089885249955270, phi_twentyTwoT_26009871450262089885249955271,
    phi_twentyTwoT_26009871450262089885249955272, phi_twentyTwoT_26009871450262089885249955273, phi_twentyTwoT_26009871450262089885249955274,
    phi_twentyTwoT_26009871450262089885249955275, phi_twentyTwoT_26009871450262089885249955276, phi_twentyTwoT_26009871450262089885249955277,
    phi_twentyTwoT_26009871450262089885249955278, phi_twentyTwoT_26009871450262089885249955279, phi_twentyTwoT_26009871450262089885249955280,
    phi_twentyTwoT_26009871450262089885249955281, phi_twentyTwoT_26009871450262089885249955282, phi_twentyTwoT_26009871450262089885249955283,
    phi_twentyTwoT_26009871450262089885249955284, phi_twentyTwoT_26009871450262089885249955285, phi_twentyTwoT_26009871450262089885249955286,
    phi_twentyTwoT_26009871450262089885249955287, phi_twentyTwoT_26009871450262089885249955288, phi_twentyTwoT_26009871450262089885249955289,
    phi_twentyTwoT_26009871450262089885249955290, phi_twentyTwoT_26009871450262089885249955291, phi_twentyTwoT_26009871450262089885249955292,
    phi_twentyTwoT_26009871450262089885249955293, phi_twentyTwoT_26009871450262089885249955294, phi_twentyTwoT_26009871450262089885249955295,
    phi_twentyTwoT_26009871450262089885249955296, phi_twentyTwoT_26009871450262089885249955297, phi_twentyTwoT_26009871450262089885249955298,
    phi_twentyTwoT_26009871450262089885249955299]

end TotientTailPeriodKiller
end Erdos249257
