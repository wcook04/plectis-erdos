import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def eightyFourCDFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem eightyFourCDFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : eightyFourCDFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [eightyFourCDFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [eightyFourCDFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then eightyFourCDFastPow a n * eightyFourCDFastPow a n * a else eightyFourCDFastPow a n * eightyFourCDFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_eightyFourCD_2 : Nat.Prime 2 := by norm_num

private theorem prime_eightyFourCD_3 : Nat.Prime 3 := by norm_num

private theorem prime_eightyFourCD_5 : Nat.Prime 5 := by norm_num

private theorem prime_eightyFourCD_7 : Nat.Prime 7 := by norm_num

private theorem prime_eightyFourCD_11 : Nat.Prime 11 := by norm_num

private theorem prime_eightyFourCD_13 : Nat.Prime 13 := by norm_num

private theorem prime_eightyFourCD_17 : Nat.Prime 17 := by norm_num

private theorem prime_eightyFourCD_19 : Nat.Prime 19 := by norm_num

private theorem prime_eightyFourCD_23 : Nat.Prime 23 := by norm_num

private theorem prime_eightyFourCD_29 : Nat.Prime 29 := by norm_num

private theorem prime_eightyFourCD_31 : Nat.Prime 31 := by norm_num

private theorem prime_eightyFourCD_37 : Nat.Prime 37 := by norm_num

private theorem prime_eightyFourCD_41 : Nat.Prime 41 := by norm_num

private theorem prime_eightyFourCD_43 : Nat.Prime 43 := by norm_num

private theorem prime_eightyFourCD_47 : Nat.Prime 47 := by norm_num

private theorem prime_eightyFourCD_53 : Nat.Prime 53 := by norm_num

private theorem prime_eightyFourCD_59 : Nat.Prime 59 := by norm_num

private theorem prime_eightyFourCD_61 : Nat.Prime 61 := by norm_num

private theorem prime_eightyFourCD_67 : Nat.Prime 67 := by norm_num

private theorem prime_eightyFourCD_71 : Nat.Prime 71 := by norm_num

private theorem prime_eightyFourCD_73 : Nat.Prime 73 := by norm_num

private theorem prime_eightyFourCD_79 : Nat.Prime 79 := by norm_num

private theorem prime_eightyFourCD_83 : Nat.Prime 83 := by norm_num

private theorem prime_eightyFourCD_89 : Nat.Prime 89 := by norm_num

private theorem prime_eightyFourCD_97 : Nat.Prime 97 := by norm_num

private theorem prime_eightyFourCD_101 : Nat.Prime 101 := by norm_num

private theorem prime_eightyFourCD_103 : Nat.Prime 103 := by norm_num

private theorem prime_eightyFourCD_107 : Nat.Prime 107 := by norm_num

private theorem prime_eightyFourCD_109 : Nat.Prime 109 := by norm_num

private theorem prime_eightyFourCD_113 : Nat.Prime 113 := by norm_num

private theorem prime_eightyFourCD_127 : Nat.Prime 127 := by norm_num

private theorem prime_eightyFourCD_131 : Nat.Prime 131 := by norm_num

private theorem prime_eightyFourCD_137 : Nat.Prime 137 := by norm_num

private theorem prime_eightyFourCD_139 : Nat.Prime 139 := by norm_num

private theorem prime_eightyFourCD_149 : Nat.Prime 149 := by norm_num

private theorem prime_eightyFourCD_151 : Nat.Prime 151 := by norm_num

private theorem prime_eightyFourCD_157 : Nat.Prime 157 := by norm_num

private theorem prime_eightyFourCD_163 : Nat.Prime 163 := by norm_num

private theorem prime_eightyFourCD_167 : Nat.Prime 167 := by norm_num

private theorem prime_eightyFourCD_173 : Nat.Prime 173 := by norm_num

private theorem prime_eightyFourCD_179 : Nat.Prime 179 := by norm_num

private theorem prime_eightyFourCD_181 : Nat.Prime 181 := by norm_num

private theorem prime_eightyFourCD_191 : Nat.Prime 191 := by norm_num

private theorem prime_eightyFourCD_193 : Nat.Prime 193 := by norm_num

private theorem prime_eightyFourCD_197 : Nat.Prime 197 := by norm_num

private theorem prime_eightyFourCD_199 : Nat.Prime 199 := by norm_num

private theorem prime_eightyFourCD_211 : Nat.Prime 211 := by norm_num

private theorem prime_eightyFourCD_223 : Nat.Prime 223 := by norm_num

private theorem prime_eightyFourCD_227 : Nat.Prime 227 := by norm_num

private theorem prime_eightyFourCD_229 : Nat.Prime 229 := by norm_num

private theorem prime_eightyFourCD_233 : Nat.Prime 233 := by norm_num

private theorem prime_eightyFourCD_239 : Nat.Prime 239 := by norm_num

private theorem prime_eightyFourCD_241 : Nat.Prime 241 := by norm_num

private theorem prime_eightyFourCD_251 : Nat.Prime 251 := by norm_num

private theorem prime_eightyFourCD_257 : Nat.Prime 257 := by norm_num

private theorem prime_eightyFourCD_263 : Nat.Prime 263 := by norm_num

private theorem prime_eightyFourCD_269 : Nat.Prime 269 := by norm_num

private theorem prime_eightyFourCD_271 : Nat.Prime 271 := by norm_num

private theorem prime_eightyFourCD_283 : Nat.Prime 283 := by norm_num

private theorem prime_eightyFourCD_293 : Nat.Prime 293 := by norm_num

private theorem prime_eightyFourCD_313 : Nat.Prime 313 := by norm_num

private theorem prime_eightyFourCD_317 : Nat.Prime 317 := by norm_num

private theorem prime_eightyFourCD_331 : Nat.Prime 331 := by norm_num

private theorem prime_eightyFourCD_337 : Nat.Prime 337 := by norm_num

private theorem prime_eightyFourCD_347 : Nat.Prime 347 := by norm_num

private theorem prime_eightyFourCD_359 : Nat.Prime 359 := by norm_num

private theorem prime_eightyFourCD_373 : Nat.Prime 373 := by norm_num

private theorem prime_eightyFourCD_379 : Nat.Prime 379 := by norm_num

private theorem prime_eightyFourCD_383 : Nat.Prime 383 := by norm_num

private theorem prime_eightyFourCD_401 : Nat.Prime 401 := by norm_num

private theorem prime_eightyFourCD_409 : Nat.Prime 409 := by norm_num

private theorem prime_eightyFourCD_421 : Nat.Prime 421 := by norm_num

private theorem prime_eightyFourCD_439 : Nat.Prime 439 := by norm_num

private theorem prime_eightyFourCD_443 : Nat.Prime 443 := by norm_num

private theorem prime_eightyFourCD_449 : Nat.Prime 449 := by norm_num

private theorem prime_eightyFourCD_457 : Nat.Prime 457 := by norm_num

private theorem prime_eightyFourCD_461 : Nat.Prime 461 := by norm_num

private theorem prime_eightyFourCD_463 : Nat.Prime 463 := by norm_num

private theorem prime_eightyFourCD_467 : Nat.Prime 467 := by norm_num

private theorem prime_eightyFourCD_479 : Nat.Prime 479 := by norm_num

private theorem prime_eightyFourCD_487 : Nat.Prime 487 := by norm_num

private theorem prime_eightyFourCD_491 : Nat.Prime 491 := by norm_num

private theorem prime_eightyFourCD_499 : Nat.Prime 499 := by norm_num

private theorem prime_eightyFourCD_503 : Nat.Prime 503 := by norm_num

private theorem prime_eightyFourCD_509 : Nat.Prime 509 := by norm_num

private theorem prime_eightyFourCD_523 : Nat.Prime 523 := by norm_num

private theorem prime_eightyFourCD_541 : Nat.Prime 541 := by norm_num

private theorem prime_eightyFourCD_547 : Nat.Prime 547 := by norm_num

private theorem prime_eightyFourCD_593 : Nat.Prime 593 := by norm_num

private theorem prime_eightyFourCD_619 : Nat.Prime 619 := by norm_num

private theorem prime_eightyFourCD_643 : Nat.Prime 643 := by norm_num

private theorem prime_eightyFourCD_647 : Nat.Prime 647 := by norm_num

private theorem prime_eightyFourCD_659 : Nat.Prime 659 := by norm_num

private theorem prime_eightyFourCD_673 : Nat.Prime 673 := by norm_num

private theorem prime_eightyFourCD_739 : Nat.Prime 739 := by norm_num

private theorem prime_eightyFourCD_743 : Nat.Prime 743 := by norm_num

private theorem prime_eightyFourCD_829 : Nat.Prime 829 := by norm_num

private theorem prime_eightyFourCD_839 : Nat.Prime 839 := by norm_num

private theorem prime_eightyFourCD_863 : Nat.Prime 863 := by norm_num

private theorem prime_eightyFourCD_911 : Nat.Prime 911 := by norm_num

private theorem prime_eightyFourCD_937 : Nat.Prime 937 := by norm_num

private theorem prime_eightyFourCD_941 : Nat.Prime 941 := by norm_num

private theorem prime_eightyFourCD_977 : Nat.Prime 977 := by norm_num

private theorem prime_eightyFourCD_991 : Nat.Prime 991 := by norm_num

private theorem prime_eightyFourCD_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_eightyFourCD_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_eightyFourCD_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_eightyFourCD_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_eightyFourCD_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_eightyFourCD_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_eightyFourCD_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_eightyFourCD_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_eightyFourCD_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_eightyFourCD_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_eightyFourCD_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_eightyFourCD_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_eightyFourCD_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_eightyFourCD_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_eightyFourCD_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_eightyFourCD_1373 : Nat.Prime 1373 := by norm_num

private theorem prime_eightyFourCD_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_eightyFourCD_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_eightyFourCD_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_eightyFourCD_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_eightyFourCD_1483 : Nat.Prime 1483 := by norm_num

private theorem prime_eightyFourCD_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_eightyFourCD_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_eightyFourCD_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_eightyFourCD_1709 : Nat.Prime 1709 := by norm_num

private theorem prime_eightyFourCD_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_eightyFourCD_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_eightyFourCD_1867 : Nat.Prime 1867 := by norm_num

private theorem prime_eightyFourCD_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_eightyFourCD_1993 : Nat.Prime 1993 := by norm_num

private theorem prime_eightyFourCD_2087 : Nat.Prime 2087 := by norm_num

private theorem prime_eightyFourCD_2111 : Nat.Prime 2111 := by norm_num

private theorem prime_eightyFourCD_2113 : Nat.Prime 2113 := by norm_num

private theorem prime_eightyFourCD_2251 : Nat.Prime 2251 := by norm_num

private theorem prime_eightyFourCD_2281 : Nat.Prime 2281 := by norm_num

private theorem prime_eightyFourCD_2311 : Nat.Prime 2311 := by norm_num

private theorem prime_eightyFourCD_2357 : Nat.Prime 2357 := by norm_num

private theorem prime_eightyFourCD_2423 : Nat.Prime 2423 := by norm_num

private theorem prime_eightyFourCD_2551 : Nat.Prime 2551 := by norm_num

private theorem prime_eightyFourCD_2633 : Nat.Prime 2633 := by norm_num

private theorem prime_eightyFourCD_2689 : Nat.Prime 2689 := by norm_num

private theorem prime_eightyFourCD_2719 : Nat.Prime 2719 := by norm_num

private theorem prime_eightyFourCD_2731 : Nat.Prime 2731 := by norm_num

private theorem prime_eightyFourCD_2749 : Nat.Prime 2749 := by norm_num

private theorem prime_eightyFourCD_2791 : Nat.Prime 2791 := by norm_num

private theorem prime_eightyFourCD_2819 : Nat.Prime 2819 := by norm_num

private theorem prime_eightyFourCD_2851 : Nat.Prime 2851 := by norm_num

private theorem prime_eightyFourCD_2879 : Nat.Prime 2879 := by norm_num

private theorem prime_eightyFourCD_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_eightyFourCD_2963 : Nat.Prime 2963 := by norm_num

private theorem prime_eightyFourCD_3109 : Nat.Prime 3109 := by norm_num

private theorem prime_eightyFourCD_3209 : Nat.Prime 3209 := by norm_num

private theorem prime_eightyFourCD_3229 : Nat.Prime 3229 := by norm_num

private theorem prime_eightyFourCD_3271 : Nat.Prime 3271 := by norm_num

private theorem prime_eightyFourCD_3499 : Nat.Prime 3499 := by norm_num

private theorem prime_eightyFourCD_3517 : Nat.Prime 3517 := by norm_num

private theorem prime_eightyFourCD_3533 : Nat.Prime 3533 := by norm_num

private theorem prime_eightyFourCD_3637 : Nat.Prime 3637 := by norm_num

private theorem prime_eightyFourCD_3761 : Nat.Prime 3761 := by norm_num

private theorem prime_eightyFourCD_3823 : Nat.Prime 3823 := by norm_num

private theorem prime_eightyFourCD_4289 : Nat.Prime 4289 := by norm_num

private theorem prime_eightyFourCD_4349 : Nat.Prime 4349 := by norm_num

private theorem prime_eightyFourCD_4357 : Nat.Prime 4357 := by norm_num

private theorem prime_eightyFourCD_4391 : Nat.Prime 4391 := by norm_num

private theorem prime_eightyFourCD_4397 : Nat.Prime 4397 := by norm_num

private theorem prime_eightyFourCD_4583 : Nat.Prime 4583 := by norm_num

private theorem prime_eightyFourCD_4673 : Nat.Prime 4673 := by norm_num

private theorem prime_eightyFourCD_4801 : Nat.Prime 4801 := by norm_num

private theorem prime_eightyFourCD_4951 : Nat.Prime 4951 := by norm_num

private theorem prime_eightyFourCD_5381 : Nat.Prime 5381 := by norm_num

private theorem prime_eightyFourCD_5441 : Nat.Prime 5441 := by norm_num

private theorem prime_eightyFourCD_5807 : Nat.Prime 5807 := by norm_num

private theorem prime_eightyFourCD_5923 : Nat.Prime 5923 := by norm_num

private theorem prime_eightyFourCD_6547 : Nat.Prime 6547 := by norm_num

private theorem prime_eightyFourCD_6701 : Nat.Prime 6701 := by norm_num

private theorem prime_eightyFourCD_7129 : Nat.Prime 7129 := by norm_num

private theorem prime_eightyFourCD_7523 : Nat.Prime 7523 := by norm_num

private theorem prime_eightyFourCD_7589 : Nat.Prime 7589 := by norm_num

private theorem prime_eightyFourCD_7591 : Nat.Prime 7591 := by norm_num

private theorem prime_eightyFourCD_7757 : Nat.Prime 7757 := by norm_num

private theorem prime_eightyFourCD_7949 : Nat.Prime 7949 := by norm_num

private theorem prime_eightyFourCD_8191 : Nat.Prime 8191 := by norm_num

private theorem prime_eightyFourCD_8353 : Nat.Prime 8353 := by norm_num

private theorem prime_eightyFourCD_8443 : Nat.Prime 8443 := by norm_num

private theorem prime_eightyFourCD_8693 : Nat.Prime 8693 := by norm_num

private theorem prime_eightyFourCD_8747 : Nat.Prime 8747 := by norm_num

private theorem prime_eightyFourCD_8831 : Nat.Prime 8831 := by norm_num

private theorem prime_eightyFourCD_9323 : Nat.Prime 9323 := by norm_num

private theorem prime_eightyFourCD_9403 : Nat.Prime 9403 := by norm_num

private theorem prime_eightyFourCD_9413 : Nat.Prime 9413 := by norm_num

private theorem prime_eightyFourCD_9689 : Nat.Prime 9689 := by norm_num

private theorem prime_eightyFourCD_10093 : Nat.Prime 10093 := by norm_num

private theorem prime_eightyFourCD_10163 : Nat.Prime 10163 := by norm_num

private theorem prime_eightyFourCD_10181 : Nat.Prime 10181 := by norm_num

private theorem prime_eightyFourCD_10477 : Nat.Prime 10477 := by norm_num

private theorem prime_eightyFourCD_10627 : Nat.Prime 10627 := by norm_num

private theorem prime_eightyFourCD_10709 : Nat.Prime 10709 := by norm_num

private theorem prime_eightyFourCD_10883 : Nat.Prime 10883 := by norm_num

private theorem prime_eightyFourCD_11369 : Nat.Prime 11369 := by norm_num

private theorem prime_eightyFourCD_11821 : Nat.Prime 11821 := by norm_num

private theorem prime_eightyFourCD_11941 : Nat.Prime 11941 := by norm_num

private theorem prime_eightyFourCD_12211 : Nat.Prime 12211 := by norm_num

private theorem prime_eightyFourCD_12487 : Nat.Prime 12487 := by norm_num

private theorem prime_eightyFourCD_12703 : Nat.Prime 12703 := by norm_num

private theorem prime_eightyFourCD_12889 : Nat.Prime 12889 := by norm_num

private theorem prime_eightyFourCD_13291 : Nat.Prime 13291 := by norm_num

private theorem prime_eightyFourCD_13399 : Nat.Prime 13399 := by norm_num

private theorem prime_eightyFourCD_13577 : Nat.Prime 13577 := by norm_num

private theorem prime_eightyFourCD_13597 : Nat.Prime 13597 := by norm_num

private theorem prime_eightyFourCD_15683 : Nat.Prime 15683 := by norm_num

private theorem prime_eightyFourCD_16417 : Nat.Prime 16417 := by norm_num

private theorem prime_eightyFourCD_16547 : Nat.Prime 16547 := by norm_num

private theorem prime_eightyFourCD_17597 : Nat.Prime 17597 := by norm_num

private theorem prime_eightyFourCD_19079 : Nat.Prime 19079 := by norm_num

private theorem prime_eightyFourCD_19759 : Nat.Prime 19759 := by norm_num

private theorem prime_eightyFourCD_20359 : Nat.Prime 20359 := by norm_num

private theorem prime_eightyFourCD_20393 : Nat.Prime 20393 := by norm_num

private theorem prime_eightyFourCD_21139 : Nat.Prime 21139 := by norm_num

private theorem prime_eightyFourCD_22091 : Nat.Prime 22091 := by norm_num

private theorem prime_eightyFourCD_22283 : Nat.Prime 22283 := by norm_num

private theorem prime_eightyFourCD_22307 : Nat.Prime 22307 := by norm_num

private theorem prime_eightyFourCD_22651 : Nat.Prime 22651 := by norm_num

private theorem prime_eightyFourCD_23131 : Nat.Prime 23131 := by norm_num

private theorem prime_eightyFourCD_23339 : Nat.Prime 23339 := by norm_num

private theorem prime_eightyFourCD_24469 : Nat.Prime 24469 := by norm_num

private theorem prime_eightyFourCD_26119 : Nat.Prime 26119 := by norm_num

private theorem prime_eightyFourCD_27283 : Nat.Prime 27283 := by norm_num

private theorem prime_eightyFourCD_27817 : Nat.Prime 27817 := by norm_num

private theorem prime_eightyFourCD_27883 : Nat.Prime 27883 := by norm_num

private theorem prime_eightyFourCD_28447 : Nat.Prime 28447 := by norm_num

private theorem prime_eightyFourCD_28499 : Nat.Prime 28499 := by norm_num

private theorem prime_eightyFourCD_31319 : Nat.Prime 31319 := by norm_num

private theorem prime_eightyFourCD_33457 : Nat.Prime 33457 := by norm_num

private theorem prime_eightyFourCD_33563 : Nat.Prime 33563 := by norm_num

private theorem prime_eightyFourCD_34033 : Nat.Prime 34033 := by norm_num

private theorem prime_eightyFourCD_34949 : Nat.Prime 34949 := by norm_num

private theorem prime_eightyFourCD_37619 : Nat.Prime 37619 := by norm_num

private theorem prime_eightyFourCD_38299 : Nat.Prime 38299 := by norm_num

private theorem prime_eightyFourCD_46819 : Nat.Prime 46819 := by norm_num

private theorem prime_eightyFourCD_47969 : Nat.Prime 47969 := by norm_num

private theorem prime_eightyFourCD_48179 : Nat.Prime 48179 := by norm_num

private theorem prime_eightyFourCD_48271 : Nat.Prime 48271 := by norm_num

private theorem prime_eightyFourCD_48407 : Nat.Prime 48407 := by norm_num

private theorem prime_eightyFourCD_48571 : Nat.Prime 48571 := by norm_num

private theorem prime_eightyFourCD_48857 : Nat.Prime 48857 := by norm_num

private theorem prime_eightyFourCD_53401 : Nat.Prime 53401 := by norm_num

private theorem prime_eightyFourCD_56099 : Nat.Prime 56099 := by norm_num

private theorem prime_eightyFourCD_56453 : Nat.Prime 56453 := by norm_num

private theorem prime_eightyFourCD_56467 : Nat.Prime 56467 := by norm_num

private theorem prime_eightyFourCD_56779 : Nat.Prime 56779 := by norm_num

private theorem prime_eightyFourCD_57571 : Nat.Prime 57571 := by norm_num

private theorem prime_eightyFourCD_57593 : Nat.Prime 57593 := by norm_num

private theorem prime_eightyFourCD_58031 : Nat.Prime 58031 := by norm_num

private theorem prime_eightyFourCD_61441 : Nat.Prime 61441 := by norm_num

private theorem prime_eightyFourCD_62323 : Nat.Prime 62323 := by norm_num

private theorem prime_eightyFourCD_64327 : Nat.Prime 64327 := by norm_num

private theorem prime_eightyFourCD_65239 : Nat.Prime 65239 := by norm_num

private theorem prime_eightyFourCD_65617 : Nat.Prime 65617 := by norm_num

private theorem prime_eightyFourCD_70381 : Nat.Prime 70381 := by norm_num

private theorem prime_eightyFourCD_73613 : Nat.Prime 73613 := by norm_num

private theorem prime_eightyFourCD_76991 : Nat.Prime 76991 := by norm_num

private theorem prime_eightyFourCD_77137 : Nat.Prime 77137 := by norm_num

private theorem prime_eightyFourCD_78989 : Nat.Prime 78989 := by norm_num

private theorem prime_eightyFourCD_80209 : Nat.Prime 80209 := by norm_num

private theorem prime_eightyFourCD_80917 : Nat.Prime 80917 := by norm_num

private theorem prime_eightyFourCD_85199 : Nat.Prime 85199 := by norm_num

private theorem prime_eightyFourCD_89983 : Nat.Prime 89983 := by norm_num

private theorem prime_eightyFourCD_90499 : Nat.Prime 90499 := by norm_num

private theorem prime_eightyFourCD_91393 : Nat.Prime 91393 := by norm_num

private theorem prime_eightyFourCD_92369 : Nat.Prime 92369 := by norm_num

private theorem prime_eightyFourCD_93169 : Nat.Prime 93169 := by norm_num

private theorem prime_eightyFourCD_99971 : Nat.Prime 99971 := by norm_num

private theorem prime_eightyFourCD_102647 : Nat.Prime 102647 := by norm_num

private theorem prime_eightyFourCD_105373 : Nat.Prime 105373 := by norm_num

private theorem prime_eightyFourCD_110989 : Nat.Prime 110989 := by norm_num

private theorem prime_eightyFourCD_111869 : Nat.Prime 111869 := by norm_num

private theorem prime_eightyFourCD_115807 : Nat.Prime 115807 := by norm_num

private theorem prime_eightyFourCD_119447 : Nat.Prime 119447 := by norm_num

private theorem prime_eightyFourCD_121591 : Nat.Prime 121591 := by norm_num

private theorem prime_eightyFourCD_124301 : Nat.Prime 124301 := by norm_num

private theorem prime_eightyFourCD_125963 : Nat.Prime 125963 := by norm_num

private theorem prime_eightyFourCD_129893 : Nat.Prime 129893 := by norm_num

private theorem prime_eightyFourCD_138403 : Nat.Prime 138403 := by norm_num

private theorem prime_eightyFourCD_152993 : Nat.Prime 152993 := by norm_num

private theorem prime_eightyFourCD_153749 : Nat.Prime 153749 := by norm_num

private theorem prime_eightyFourCD_157907 : Nat.Prime 157907 := by norm_num

private theorem prime_eightyFourCD_158143 : Nat.Prime 158143 := by norm_num

private theorem prime_eightyFourCD_160409 : Nat.Prime 160409 := by norm_num

private theorem prime_eightyFourCD_163223 : Nat.Prime 163223 := by norm_num

private theorem prime_eightyFourCD_170179 : Nat.Prime 170179 := by norm_num

private theorem prime_eightyFourCD_184913 : Nat.Prime 184913 := by norm_num

private theorem prime_eightyFourCD_191099 : Nat.Prime 191099 := by norm_num

private theorem prime_eightyFourCD_191531 : Nat.Prime 191531 := by norm_num

private theorem prime_eightyFourCD_203591 : Nat.Prime 203591 := by norm_num

private theorem prime_eightyFourCD_223621 : Nat.Prime 223621 := by norm_num

private theorem prime_eightyFourCD_248323 : Nat.Prime 248323 := by norm_num

private theorem prime_eightyFourCD_251149 : Nat.Prime 251149 := by norm_num

private theorem prime_eightyFourCD_254857 : Nat.Prime 254857 := by norm_num

private theorem prime_eightyFourCD_255209 : Nat.Prime 255209 := by norm_num

private theorem prime_eightyFourCD_255887 : Nat.Prime 255887 := by norm_num

private theorem prime_eightyFourCD_263401 : Nat.Prime 263401 := by norm_num

private theorem prime_eightyFourCD_266977 : Nat.Prime 266977 := by norm_num

private theorem prime_eightyFourCD_272411 : Nat.Prime 272411 := by norm_num

private theorem prime_eightyFourCD_280589 : Nat.Prime 280589 := by norm_num

private theorem prime_eightyFourCD_285377 : Nat.Prime 285377 := by norm_num

private theorem prime_eightyFourCD_294551 : Nat.Prime 294551 := by norm_num

private theorem prime_eightyFourCD_323803 : Nat.Prime 323803 := by norm_num

private theorem prime_eightyFourCD_325693 : Nat.Prime 325693 := by norm_num

private theorem prime_eightyFourCD_333103 : Nat.Prime 333103 := by norm_num

private theorem prime_eightyFourCD_340643 : Nat.Prime 340643 := by norm_num

private theorem prime_eightyFourCD_342233 : Nat.Prime 342233 := by norm_num

private theorem prime_eightyFourCD_380957 : Nat.Prime 380957 := by norm_num

private theorem prime_eightyFourCD_400871 : Nat.Prime 400871 := by norm_num

private theorem prime_eightyFourCD_406993 : Nat.Prime 406993 := by norm_num

private theorem prime_eightyFourCD_495133 : Nat.Prime 495133 := by norm_num

private theorem prime_eightyFourCD_520393 : Nat.Prime 520393 := by norm_num

private theorem prime_eightyFourCD_540383 : Nat.Prime 540383 := by norm_num

private theorem prime_eightyFourCD_542951 : Nat.Prime 542951 := by norm_num

private theorem prime_eightyFourCD_573161 : Nat.Prime 573161 := by norm_num

private theorem prime_eightyFourCD_593071 : Nat.Prime 593071 := by norm_num

private theorem prime_eightyFourCD_605629 : Nat.Prime 605629 := by norm_num

private theorem prime_eightyFourCD_616219 : Nat.Prime 616219 := by norm_num

private theorem prime_eightyFourCD_662527 : Nat.Prime 662527 := by norm_num

private theorem prime_eightyFourCD_703349 : Nat.Prime 703349 := by norm_num

private theorem prime_eightyFourCD_707177 : Nat.Prime 707177 := by norm_num

private theorem prime_eightyFourCD_794491 : Nat.Prime 794491 := by norm_num

private theorem prime_eightyFourCD_798179 : Nat.Prime 798179 := by norm_num

private theorem prime_eightyFourCD_800161 : Nat.Prime 800161 := by norm_num

private theorem prime_eightyFourCD_815713 : Nat.Prime 815713 := by norm_num

private theorem prime_eightyFourCD_840181 : Nat.Prime 840181 := by norm_num

private theorem prime_eightyFourCD_859121 : Nat.Prime 859121 := by norm_num

private theorem prime_eightyFourCD_917003 : Nat.Prime 917003 := by norm_num

private theorem prime_eightyFourCD_930079 : Nat.Prime 930079 := by norm_num

private theorem prime_eightyFourCD_1081231 : Nat.Prime 1081231 := by norm_num

private theorem prime_eightyFourCD_1118519 : Nat.Prime 1118519 := by norm_num

private theorem prime_eightyFourCD_1134271 : Nat.Prime 1134271 := by norm_num

private theorem prime_eightyFourCD_1169879 : Nat.Prime 1169879 := by norm_num

private theorem prime_eightyFourCD_1183409 : Nat.Prime 1183409 := by norm_num

private theorem prime_eightyFourCD_1209577 : Nat.Prime 1209577 := by norm_num

private theorem prime_eightyFourCD_1213673 : Nat.Prime 1213673 := by norm_num

private theorem prime_eightyFourCD_1241437 : Nat.Prime 1241437 := by norm_num

private theorem prime_eightyFourCD_1252903 : Nat.Prime 1252903 := by norm_num

private theorem prime_eightyFourCD_1324199 : Nat.Prime 1324199 := by norm_num

private theorem prime_eightyFourCD_1325923 : Nat.Prime 1325923 := by norm_num

private theorem prime_eightyFourCD_1326971 : Nat.Prime 1326971 := by norm_num

private theorem prime_eightyFourCD_1381621 : Nat.Prime 1381621 := by norm_num

private theorem prime_eightyFourCD_1424939 : Nat.Prime 1424939 := by norm_num

private theorem prime_eightyFourCD_1444753 : Nat.Prime 1444753 := by norm_num

private theorem prime_eightyFourCD_1577201 : Nat.Prime 1577201 := by norm_num

private theorem prime_eightyFourCD_1590221 : Nat.Prime 1590221 := by norm_num

private theorem prime_eightyFourCD_1632569 : Nat.Prime 1632569 := by norm_num

private theorem prime_eightyFourCD_1666523 : Nat.Prime 1666523 := by norm_num

private theorem prime_eightyFourCD_1788229 : Nat.Prime 1788229 := by norm_num

private theorem prime_eightyFourCD_1929923 : Nat.Prime 1929923 := by norm_num

private theorem prime_eightyFourCD_2001799 : Nat.Prime 2001799 := by norm_num

private theorem prime_eightyFourCD_2032711 : Nat.Prime 2032711 := by norm_num

private theorem prime_eightyFourCD_2070473 : Nat.Prime 2070473 := by norm_num

private theorem prime_eightyFourCD_2079433 : Nat.Prime 2079433 := by norm_num

private theorem prime_eightyFourCD_2118667 : Nat.Prime 2118667 := by norm_num

private theorem prime_eightyFourCD_2278139 : Nat.Prime 2278139 := by norm_num

private theorem prime_eightyFourCD_2377703 : Nat.Prime 2377703 := by norm_num

private theorem prime_eightyFourCD_2407507 : Nat.Prime 2407507 := by norm_num

private theorem prime_eightyFourCD_2509841 : Nat.Prime 2509841 := by norm_num

private theorem prime_eightyFourCD_2744257 : Nat.Prime 2744257 := by norm_num

private theorem prime_eightyFourCD_2984351 : Nat.Prime 2984351 := by norm_num

private theorem prime_eightyFourCD_2993687 : Nat.Prime 2993687 := by norm_num

private theorem prime_eightyFourCD_3059341 : Nat.Prime 3059341 := by norm_num

private theorem prime_eightyFourCD_3126131 : Nat.Prime 3126131 := by norm_num

private theorem prime_eightyFourCD_3145633 : Nat.Prime 3145633 := by norm_num

private theorem prime_eightyFourCD_3424459 : Nat.Prime 3424459 := by norm_num

private theorem prime_eightyFourCD_3447443 : Nat.Prime 3447443 := by norm_num

private theorem prime_eightyFourCD_3559747 : Nat.Prime 3559747 := by norm_num

private theorem prime_eightyFourCD_3733111 : Nat.Prime 3733111 := by norm_num

private theorem prime_eightyFourCD_3889913 : Nat.Prime 3889913 := by norm_num

private theorem prime_eightyFourCD_3901867 : Nat.Prime 3901867 := by norm_num

private theorem prime_eightyFourCD_4076257 : Nat.Prime 4076257 := by norm_num

private theorem prime_eightyFourCD_4592453 : Nat.Prime 4592453 := by norm_num

private theorem prime_eightyFourCD_4864177 : Nat.Prime 4864177 := by norm_num

private theorem prime_eightyFourCD_4946759 : Nat.Prime 4946759 := by norm_num

private theorem prime_eightyFourCD_5102731 : Nat.Prime 5102731 := by norm_num

private theorem prime_eightyFourCD_5432521 : Nat.Prime 5432521 := by norm_num

private theorem prime_eightyFourCD_5490883 : Nat.Prime 5490883 := by norm_num

private theorem prime_eightyFourCD_5806987 : Nat.Prime 5806987 := by norm_num

private theorem prime_eightyFourCD_5814199 : Nat.Prime 5814199 := by norm_num

private theorem prime_eightyFourCD_6199399 : Nat.Prime 6199399 := by norm_num

private theorem prime_eightyFourCD_6311623 : Nat.Prime 6311623 := by norm_num

private theorem prime_eightyFourCD_6388337 : Nat.Prime 6388337 := by norm_num

private theorem prime_eightyFourCD_6406111 : Nat.Prime 6406111 := by norm_num

private theorem prime_eightyFourCD_7006823 : Nat.Prime 7006823 := by norm_num

private theorem prime_eightyFourCD_7890919 : Nat.Prime 7890919 := by norm_num

private theorem prime_eightyFourCD_8564053 : Nat.Prime 8564053 := by norm_num

private theorem prime_eightyFourCD_8597027 : Nat.Prime 8597027 := by norm_num

private theorem prime_eightyFourCD_9004361 : Nat.Prime 9004361 := by norm_num

private theorem prime_eightyFourCD_9208417 : Nat.Prime 9208417 := by norm_num

private theorem prime_eightyFourCD_9425329 : Nat.Prime 9425329 := by norm_num

private theorem prime_eightyFourCD_10001443 : Nat.Prime 10001443 := by norm_num

private theorem prime_eightyFourCD_10191647 : Nat.Prime 10191647 := by norm_num

private theorem prime_eightyFourCD_10204903 : Nat.Prime 10204903 := by norm_num

private theorem prime_eightyFourCD_10274591 : Nat.Prime 10274591 := by norm_num

private theorem prime_eightyFourCD_11824817 : Nat.Prime 11824817 := by norm_num

private theorem prime_eightyFourCD_11927347 : Nat.Prime 11927347 := by norm_num

private theorem prime_eightyFourCD_12807089 : Nat.Prime 12807089 := by norm_num

private theorem prime_eightyFourCD_14880373 : Nat.Prime 14880373 := by norm_num

private theorem prime_eightyFourCD_15218597 : Nat.Prime 15218597 := by norm_num

private theorem prime_eightyFourCD_16902959 : Nat.Prime 16902959 := by norm_num

private theorem prime_eightyFourCD_18338653 : Nat.Prime 18338653 := by norm_num

private theorem prime_eightyFourCD_19233031 : Nat.Prime 19233031 := by norm_num

private theorem prime_eightyFourCD_20687839 : Nat.Prime 20687839 := by norm_num

private theorem prime_eightyFourCD_21068717 : Nat.Prime 21068717 := by norm_num

private theorem prime_eightyFourCD_23275897 : Nat.Prime 23275897 := by norm_num

private theorem prime_eightyFourCD_24589739 : Nat.Prime 24589739 := by norm_num

private theorem prime_eightyFourCD_27318007 : Nat.Prime 27318007 := by norm_num

private theorem prime_eightyFourCD_27620941 : Nat.Prime 27620941 := by norm_num

private theorem prime_eightyFourCD_33310301 : Nat.Prime 33310301 := by
  apply lucas_primality 33310301 (2 : ZMod 33310301)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (333103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (333103, 1)] : List FactorBlock).map factorBlockValue).prod) = 33310301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_333103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33310301) ^ 16655150 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 33310301) ^ 6662060 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 33310301) ^ 100 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_34256213 : Nat.Prime 34256213 := by
  apply lucas_primality 34256213 (2 : ZMod 34256213)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8564053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8564053, 1)] : List FactorBlock).map factorBlockValue).prod) = 34256213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_8564053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 34256213) ^ 17128106 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 34256213) ^ 4 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_39116107 : Nat.Prime 39116107 := by
  apply lucas_primality 39116107 (2 : ZMod 39116107)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (673, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (673, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) = 39116107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_673
      · exact prime_eightyFourCD_3229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39116107) ^ 19558053 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 39116107) ^ 13038702 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 39116107) ^ 58122 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 39116107) ^ 12114 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_39248123 : Nat.Prime 39248123 := by
  apply lucas_primality 39248123 (2 : ZMod 39248123)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2087, 1), (9403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2087, 1), (9403, 1)] : List FactorBlock).map factorBlockValue).prod) = 39248123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_2087
      · exact prime_eightyFourCD_9403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39248123) ^ 19624061 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 39248123) ^ 18806 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 39248123) ^ 4174 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_48865591 : Nat.Prime 48865591 := by
  apply lucas_primality 48865591 (6 : ZMod 48865591)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (542951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (542951, 1)] : List FactorBlock).map factorBlockValue).prod) = 48865591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_542951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 48865591) ^ 24432795 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 48865591) ^ 16288530 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 48865591) ^ 9773118 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 48865591) ^ 90 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_51632771 : Nat.Prime 51632771 := by
  apply lucas_primality 51632771 (7 : ZMod 51632771)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (105373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (105373, 1)] : List FactorBlock).map factorBlockValue).prod) = 51632771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_105373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 51632771) ^ 25816385 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 51632771) ^ 10326554 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 51632771) ^ 7376110 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 51632771) ^ 490 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_52644989 : Nat.Prime 52644989 := by
  apply lucas_primality 52644989 (2 : ZMod 52644989)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (17, 1), (70381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (17, 1), (70381, 1)] : List FactorBlock).map factorBlockValue).prod) = 52644989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_17
      · exact prime_eightyFourCD_70381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 52644989) ^ 26322494 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 52644989) ^ 4785908 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 52644989) ^ 3096764 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 52644989) ^ 748 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_52817077 : Nat.Prime 52817077 := by
  apply lucas_primality 52817077 (5 : ZMod 52817077)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (37619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (37619, 1)] : List FactorBlock).map factorBlockValue).prod) = 52817077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_37619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 52817077) ^ 26408538 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 52817077) ^ 17605692 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 52817077) ^ 4062852 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 52817077) ^ 1404 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_57486973 : Nat.Prime 57486973 := by
  apply lucas_primality 57486973 (2 : ZMod 57486973)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1091, 1), (4391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1091, 1), (4391, 1)] : List FactorBlock).map factorBlockValue).prod) = 57486973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_1091
      · exact prime_eightyFourCD_4391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57486973) ^ 28743486 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 57486973) ^ 19162324 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 57486973) ^ 52692 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 57486973) ^ 13092 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_65190253 : Nat.Prime 65190253 := by
  apply lucas_primality 65190253 (2 : ZMod 65190253)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5432521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5432521, 1)] : List FactorBlock).map factorBlockValue).prod) = 65190253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5432521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 65190253) ^ 32595126 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 65190253) ^ 21730084 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 65190253) ^ 12 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_71097181 : Nat.Prime 71097181 := by
  apply lucas_primality 71097181 (14 : ZMod 71097181)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 2), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 2), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) = 71097181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_1399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 71097181) ^ 35548590 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (14 : ZMod 71097181) ^ 23699060 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (14 : ZMod 71097181) ^ 14219436 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (14 : ZMod 71097181) ^ 10156740 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (14 : ZMod 71097181) ^ 6463380 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (14 : ZMod 71097181) ^ 50820 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_75382193 : Nat.Prime 75382193 := by
  apply lucas_primality 75382193 (3 : ZMod 75382193)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (97, 1), (48571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (97, 1), (48571, 1)] : List FactorBlock).map factorBlockValue).prod) = 75382193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_97
      · exact prime_eightyFourCD_48571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 75382193) ^ 37691096 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 75382193) ^ 777136 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 75382193) ^ 1552 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_81705343 : Nat.Prime 81705343 := by
  apply lucas_primality 81705343 (6 : ZMod 81705343)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149, 1), (91393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149, 1), (91393, 1)] : List FactorBlock).map factorBlockValue).prod) = 81705343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_149
      · exact prime_eightyFourCD_91393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 81705343) ^ 40852671 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 81705343) ^ 27235114 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 81705343) ^ 548358 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 81705343) ^ 894 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_83991847 : Nat.Prime 83991847 := by
  apply lucas_primality 83991847 (5 : ZMod 83991847)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (173, 1), (80917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (173, 1), (80917, 1)] : List FactorBlock).map factorBlockValue).prod) = 83991847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_173
      · exact prime_eightyFourCD_80917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 83991847) ^ 41995923 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 83991847) ^ 27997282 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 83991847) ^ 485502 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 83991847) ^ 1038 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_90045533 : Nat.Prime 90045533 := by
  apply lucas_primality 90045533 (2 : ZMod 90045533)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (1324199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (1324199, 1)] : List FactorBlock).map factorBlockValue).prod) = 90045533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_17
      · exact prime_eightyFourCD_1324199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 90045533) ^ 45022766 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 90045533) ^ 5296796 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 90045533) ^ 68 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_102102157 : Nat.Prime 102102157 := by
  apply lucas_primality 102102157 (2 : ZMod 102102157)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (29, 1), (7523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (29, 1), (7523, 1)] : List FactorBlock).map factorBlockValue).prod) = 102102157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_29
      · exact prime_eightyFourCD_7523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 102102157) ^ 51051078 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 102102157) ^ 34034052 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 102102157) ^ 7854012 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 102102157) ^ 3520764 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 102102157) ^ 13572 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_104375879 : Nat.Prime 104375879 := by
  apply lucas_primality 104375879 (11 : ZMod 104375879)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (1213673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (1213673, 1)] : List FactorBlock).map factorBlockValue).prod) = 104375879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_43
      · exact prime_eightyFourCD_1213673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 104375879) ^ 52187939 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 104375879) ^ 2427346 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 104375879) ^ 86 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_104376971 : Nat.Prime 104376971 := by
  apply lucas_primality 104376971 (6 : ZMod 104376971)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (113, 1), (92369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (113, 1), (92369, 1)] : List FactorBlock).map factorBlockValue).prod) = 104376971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_113
      · exact prime_eightyFourCD_92369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 104376971) ^ 52188485 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 104376971) ^ 20875394 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 104376971) ^ 923690 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 104376971) ^ 1130 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_109967489 : Nat.Prime 109967489 := by
  apply lucas_primality 109967489 (3 : ZMod 109967489)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (859121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (859121, 1)] : List FactorBlock).map factorBlockValue).prod) = 109967489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_859121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 109967489) ^ 54983744 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 109967489) ^ 128 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_111331093 : Nat.Prime 111331093 := by
  apply lucas_primality 111331093 (2 : ZMod 111331093)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (151, 1), (61441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (151, 1), (61441, 1)] : List FactorBlock).map factorBlockValue).prod) = 111331093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_151
      · exact prime_eightyFourCD_61441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 111331093) ^ 55665546 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 111331093) ^ 37110364 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 111331093) ^ 737292 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 111331093) ^ 1812 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_123295093 : Nat.Prime 123295093 := by
  apply lucas_primality 123295093 (5 : ZMod 123295093)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (10274591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (10274591, 1)] : List FactorBlock).map factorBlockValue).prod) = 123295093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_10274591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 123295093) ^ 61647546 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 123295093) ^ 41098364 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 123295093) ^ 12 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_138302051 : Nat.Prime 138302051 := by
  apply lucas_primality 138302051 (2 : ZMod 138302051)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (467, 1), (5923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (467, 1), (5923, 1)] : List FactorBlock).map factorBlockValue).prod) = 138302051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_467
      · exact prime_eightyFourCD_5923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 138302051) ^ 69151025 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 138302051) ^ 27660410 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 138302051) ^ 296150 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 138302051) ^ 23350 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_142389881 : Nat.Prime 142389881 := by
  apply lucas_primality 142389881 (3 : ZMod 142389881)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (3559747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (3559747, 1)] : List FactorBlock).map factorBlockValue).prod) = 142389881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_3559747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 142389881) ^ 71194940 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 142389881) ^ 28477976 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 142389881) ^ 40 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_146409983 : Nat.Prime 146409983 := by
  apply lucas_primality 146409983 (5 : ZMod 146409983)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (137, 1), (11369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (137, 1), (11369, 1)] : List FactorBlock).map factorBlockValue).prod) = 146409983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_47
      · exact prime_eightyFourCD_137
      · exact prime_eightyFourCD_11369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 146409983) ^ 73204991 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 146409983) ^ 3115106 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 146409983) ^ 1068686 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 146409983) ^ 12878 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_175206259 : Nat.Prime 175206259 := by
  apply lucas_primality 175206259 (10 : ZMod 175206259)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (467, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (467, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) = 175206259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_19
      · exact prime_eightyFourCD_467
      · exact prime_eightyFourCD_1097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 175206259) ^ 87603129 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 175206259) ^ 58402086 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 175206259) ^ 9221382 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 175206259) ^ 375174 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 175206259) ^ 159714 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_176811091 : Nat.Prime 176811091 := by
  apply lucas_primality 176811091 (2 : ZMod 176811091)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (359, 1), (16417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (359, 1), (16417, 1)] : List FactorBlock).map factorBlockValue).prod) = 176811091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_359
      · exact prime_eightyFourCD_16417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 176811091) ^ 88405545 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 176811091) ^ 58937030 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 176811091) ^ 35362218 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 176811091) ^ 492510 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 176811091) ^ 10770 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_183581171 : Nat.Prime 183581171 := by
  apply lucas_primality 183581171 (2 : ZMod 183581171)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (798179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (798179, 1)] : List FactorBlock).map factorBlockValue).prod) = 183581171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_23
      · exact prime_eightyFourCD_798179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 183581171) ^ 91790585 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 183581171) ^ 36716234 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 183581171) ^ 7981790 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 183581171) ^ 230 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_208751759 : Nat.Prime 208751759 := by
  apply lucas_primality 208751759 (13 : ZMod 208751759)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (104375879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (104375879, 1)] : List FactorBlock).map factorBlockValue).prod) = 208751759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_104375879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 208751759) ^ 104375879 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 208751759) ^ 2 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_214392721 : Nat.Prime 214392721 := by
  apply lucas_primality 214392721 (57 : ZMod 214392721)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (379, 1), (2357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (379, 1), (2357, 1)] : List FactorBlock).map factorBlockValue).prod) = 214392721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_379
      · exact prime_eightyFourCD_2357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (57 : ZMod 214392721) ^ 107196360 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (57 : ZMod 214392721) ^ 71464240 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (57 : ZMod 214392721) ^ 42878544 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (57 : ZMod 214392721) ^ 565680 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (57 : ZMod 214392721) ^ 90960 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_233789029 : Nat.Prime 233789029 := by
  apply lucas_primality 233789029 (2 : ZMod 233789029)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (839, 1), (2111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (839, 1), (2111, 1)] : List FactorBlock).map factorBlockValue).prod) = 233789029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_839
      · exact prime_eightyFourCD_2111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 233789029) ^ 116894514 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 233789029) ^ 77929676 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 233789029) ^ 21253548 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 233789029) ^ 278652 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 233789029) ^ 110748 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_274503071 : Nat.Prime 274503071 := by
  apply lucas_primality 274503071 (13 : ZMod 274503071)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (1444753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (1444753, 1)] : List FactorBlock).map factorBlockValue).prod) = 274503071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_19
      · exact prime_eightyFourCD_1444753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 274503071) ^ 137251535 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 274503071) ^ 54900614 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 274503071) ^ 14447530 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 274503071) ^ 190 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_275864473 : Nat.Prime 275864473 := by
  apply lucas_primality 275864473 (7 : ZMod 275864473)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (29, 1), (10163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (29, 1), (10163, 1)] : List FactorBlock).map factorBlockValue).prod) = 275864473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_29
      · exact prime_eightyFourCD_10163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 275864473) ^ 137932236 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 275864473) ^ 91954824 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 275864473) ^ 21220344 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 275864473) ^ 9512568 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 275864473) ^ 27144 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_303445237 : Nat.Prime 303445237 := by
  apply lucas_primality 303445237 (6 : ZMod 303445237)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (815713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (815713, 1)] : List FactorBlock).map factorBlockValue).prod) = 303445237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_31
      · exact prime_eightyFourCD_815713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 303445237) ^ 151722618 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 303445237) ^ 101148412 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 303445237) ^ 9788556 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 303445237) ^ 372 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_366899293 : Nat.Prime 366899293 := by
  apply lucas_primality 366899293 (6 : ZMod 366899293)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (10191647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (10191647, 1)] : List FactorBlock).map factorBlockValue).prod) = 366899293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_10191647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 366899293) ^ 183449646 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 366899293) ^ 122299764 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 366899293) ^ 36 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_403450367 : Nat.Prime 403450367 := by
  apply lucas_primality 403450367 (5 : ZMod 403450367)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (18338653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (18338653, 1)] : List FactorBlock).map factorBlockValue).prod) = 403450367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_18338653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 403450367) ^ 201725183 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 403450367) ^ 36677306 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 403450367) ^ 22 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_437078303 : Nat.Prime 437078303 := by
  apply lucas_primality 437078303 (5 : ZMod 437078303)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (2993687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (2993687, 1)] : List FactorBlock).map factorBlockValue).prod) = 437078303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_73
      · exact prime_eightyFourCD_2993687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 437078303) ^ 218539151 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 437078303) ^ 5987374 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 437078303) ^ 146 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_547802603 : Nat.Prime 547802603 := by
  apply lucas_primality 547802603 (2 : ZMod 547802603)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (383, 1), (479, 1), (1493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (383, 1), (479, 1), (1493, 1)] : List FactorBlock).map factorBlockValue).prod) = 547802603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_383
      · exact prime_eightyFourCD_479
      · exact prime_eightyFourCD_1493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 547802603) ^ 273901301 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 547802603) ^ 1430294 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 547802603) ^ 1143638 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 547802603) ^ 366914 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_586242073 : Nat.Prime 586242073 := by
  apply lucas_primality 586242073 (11 : ZMod 586242073)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 2), (48179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 2), (48179, 1)] : List FactorBlock).map factorBlockValue).prod) = 586242073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_48179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 586242073) ^ 293121036 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 586242073) ^ 195414024 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 586242073) ^ 45095544 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 586242073) ^ 12168 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_617540423 : Nat.Prime 617540423 := by
  apply lucas_primality 617540423 (5 : ZMod 617540423)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (439, 1), (703349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (439, 1), (703349, 1)] : List FactorBlock).map factorBlockValue).prod) = 617540423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_439
      · exact prime_eightyFourCD_703349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 617540423) ^ 308770211 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 617540423) ^ 1406698 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 617540423) ^ 878 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_671111401 : Nat.Prime 671111401 := by
  apply lucas_primality 671111401 (19 : ZMod 671111401)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (1118519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (1118519, 1)] : List FactorBlock).map factorBlockValue).prod) = 671111401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_1118519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 671111401) ^ 335555700 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (19 : ZMod 671111401) ^ 223703800 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (19 : ZMod 671111401) ^ 134222280 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (19 : ZMod 671111401) ^ 600 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_692721847 : Nat.Prime 692721847 := by
  apply lucas_primality 692721847 (3 : ZMod 692721847)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (1241437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (1241437, 1)] : List FactorBlock).map factorBlockValue).prod) = 692721847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_31
      · exact prime_eightyFourCD_1241437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 692721847) ^ 346360923 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 692721847) ^ 230907282 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 692721847) ^ 22345866 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 692721847) ^ 558 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_706637293 : Nat.Prime 706637293 := by
  apply lucas_primality 706637293 (2 : ZMod 706637293)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (1252903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (1252903, 1)] : List FactorBlock).map factorBlockValue).prod) = 706637293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_47
      · exact prime_eightyFourCD_1252903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 706637293) ^ 353318646 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 706637293) ^ 235545764 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 706637293) ^ 15034836 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 706637293) ^ 564 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_929386597 : Nat.Prime 929386597 := by
  apply lucas_primality 929386597 (5 : ZMod 929386597)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (4076257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (4076257, 1)] : List FactorBlock).map factorBlockValue).prod) = 929386597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_19
      · exact prime_eightyFourCD_4076257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 929386597) ^ 464693298 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 929386597) ^ 309795532 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 929386597) ^ 48915084 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 929386597) ^ 228 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_950405447 : Nat.Prime 950405447 := by
  apply lucas_primality 950405447 (5 : ZMod 950405447)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3823, 1), (124301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3823, 1), (124301, 1)] : List FactorBlock).map factorBlockValue).prod) = 950405447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3823
      · exact prime_eightyFourCD_124301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 950405447) ^ 475202723 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 950405447) ^ 248602 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 950405447) ^ 7646 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_965119747 : Nat.Prime 965119747 := by
  apply lucas_primality 965119747 (2 : ZMod 965119747)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (1459, 1), (2689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (1459, 1), (2689, 1)] : List FactorBlock).map factorBlockValue).prod) = 965119747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_41
      · exact prime_eightyFourCD_1459
      · exact prime_eightyFourCD_2689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 965119747) ^ 482559873 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 965119747) ^ 321706582 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 965119747) ^ 23539506 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 965119747) ^ 661494 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 965119747) ^ 358914 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1052451977 : Nat.Prime 1052451977 := by
  apply lucas_primality 1052451977 (3 : ZMod 1052451977)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (829, 1), (4289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (829, 1), (4289, 1)] : List FactorBlock).map factorBlockValue).prod) = 1052451977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_37
      · exact prime_eightyFourCD_829
      · exact prime_eightyFourCD_4289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1052451977) ^ 526225988 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1052451977) ^ 28444648 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1052451977) ^ 1269544 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1052451977) ^ 245384 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1096679393 : Nat.Prime 1096679393 := by
  apply lucas_primality 1096679393 (3 : ZMod 1096679393)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (53, 1), (34033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (53, 1), (34033, 1)] : List FactorBlock).map factorBlockValue).prod) = 1096679393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_19
      · exact prime_eightyFourCD_53
      · exact prime_eightyFourCD_34033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1096679393) ^ 548339696 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1096679393) ^ 57719968 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1096679393) ^ 20692064 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1096679393) ^ 32224 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1103457893 : Nat.Prime 1103457893 := by
  apply lucas_primality 1103457893 (2 : ZMod 1103457893)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (275864473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (275864473, 1)] : List FactorBlock).map factorBlockValue).prod) = 1103457893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_275864473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1103457893) ^ 551728946 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1103457893) ^ 4 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1162074659 : Nat.Prime 1162074659 := by
  apply lucas_primality 1162074659 (2 : ZMod 1162074659)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9323, 1), (62323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9323, 1), (62323, 1)] : List FactorBlock).map factorBlockValue).prod) = 1162074659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_9323
      · exact prime_eightyFourCD_62323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1162074659) ^ 581037329 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1162074659) ^ 124646 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1162074659) ^ 18646 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1213780949 : Nat.Prime 1213780949 := by
  apply lucas_primality 1213780949 (2 : ZMod 1213780949)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (303445237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (303445237, 1)] : List FactorBlock).map factorBlockValue).prod) = 1213780949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_303445237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1213780949) ^ 606890474 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1213780949) ^ 4 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1218456053 : Nat.Prime 1218456053 := by
  apply lucas_primality 1218456053 (2 : ZMod 1218456053)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (359, 1), (77137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (359, 1), (77137, 1)] : List FactorBlock).map factorBlockValue).prod) = 1218456053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_359
      · exact prime_eightyFourCD_77137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1218456053) ^ 609228026 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1218456053) ^ 110768732 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1218456053) ^ 3394028 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1218456053) ^ 15796 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1247161051 : Nat.Prime 1247161051 := by
  apply lucas_primality 1247161051 (2 : ZMod 1247161051)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 2), (102647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 2), (102647, 1)] : List FactorBlock).map factorBlockValue).prod) = 1247161051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_102647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1247161051) ^ 623580525 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1247161051) ^ 415720350 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1247161051) ^ 249432210 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1247161051) ^ 12150 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1252523653 : Nat.Prime 1252523653 := by
  apply lucas_primality 1252523653 (7 : ZMod 1252523653)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (104376971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (104376971, 1)] : List FactorBlock).map factorBlockValue).prod) = 1252523653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_104376971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1252523653) ^ 626261826 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1252523653) ^ 417507884 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1252523653) ^ 12 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1264086919 : Nat.Prime 1264086919 := by
  apply lucas_primality 1264086919 (3 : ZMod 1264086919)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (59, 1), (23339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (59, 1), (23339, 1)] : List FactorBlock).map factorBlockValue).prod) = 1264086919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_17
      · exact prime_eightyFourCD_59
      · exact prime_eightyFourCD_23339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1264086919) ^ 632043459 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1264086919) ^ 421362306 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1264086919) ^ 74358054 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1264086919) ^ 21425202 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1264086919) ^ 54162 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1404831863 : Nat.Prime 1404831863 := by
  apply lucas_primality 1404831863 (7 : ZMod 1404831863)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (29, 1), (181, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (29, 1), (181, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) = 1404831863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_29
      · exact prime_eightyFourCD_181
      · exact prime_eightyFourCD_2731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1404831863) ^ 702415931 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1404831863) ^ 200690266 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1404831863) ^ 48442478 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1404831863) ^ 7761502 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1404831863) ^ 514402 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1405578271 : Nat.Prime 1405578271 := by
  apply lucas_primality 1405578271 (11 : ZMod 1405578271)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (79, 1), (593071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (79, 1), (593071, 1)] : List FactorBlock).map factorBlockValue).prod) = 1405578271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_79
      · exact prime_eightyFourCD_593071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1405578271) ^ 702789135 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1405578271) ^ 468526090 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1405578271) ^ 281115654 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1405578271) ^ 17792130 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1405578271) ^ 2370 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1455847711 : Nat.Prime 1455847711 := by
  apply lucas_primality 1455847711 (3 : ZMod 1455847711)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (149, 1), (325693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (149, 1), (325693, 1)] : List FactorBlock).map factorBlockValue).prod) = 1455847711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_149
      · exact prime_eightyFourCD_325693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1455847711) ^ 727923855 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1455847711) ^ 485282570 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1455847711) ^ 291169542 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1455847711) ^ 9770790 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1455847711) ^ 4470 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1489657409 : Nat.Prime 1489657409 := by
  apply lucas_primality 1489657409 (3 : ZMod 1489657409)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (23275897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (23275897, 1)] : List FactorBlock).map factorBlockValue).prod) = 1489657409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_23275897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1489657409) ^ 744828704 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1489657409) ^ 64 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1615755517 : Nat.Prime 1615755517 := by
  apply lucas_primality 1615755517 (5 : ZMod 1615755517)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (37, 1), (191531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (37, 1), (191531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1615755517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_19
      · exact prime_eightyFourCD_37
      · exact prime_eightyFourCD_191531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1615755517) ^ 807877758 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1615755517) ^ 538585172 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1615755517) ^ 85039764 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1615755517) ^ 43669068 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1615755517) ^ 8436 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1734901199 : Nat.Prime 1734901199 := by
  apply lucas_primality 1734901199 (11 : ZMod 1734901199)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (223, 1), (3889913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (223, 1), (3889913, 1)] : List FactorBlock).map factorBlockValue).prod) = 1734901199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_223
      · exact prime_eightyFourCD_3889913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1734901199) ^ 867450599 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1734901199) ^ 7779826 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1734901199) ^ 446 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1910460449 : Nat.Prime 1910460449 := by
  apply lucas_primality 1910460449 (3 : ZMod 1910460449)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (4592453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (4592453, 1)] : List FactorBlock).map factorBlockValue).prod) = 1910460449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_4592453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1910460449) ^ 955230224 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1910460449) ^ 146958496 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1910460449) ^ 416 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1945728377 : Nat.Prime 1945728377 := by
  apply lucas_primality 1945728377 (3 : ZMod 1945728377)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (911, 1), (266977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (911, 1), (266977, 1)] : List FactorBlock).map factorBlockValue).prod) = 1945728377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_911
      · exact prime_eightyFourCD_266977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1945728377) ^ 972864188 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1945728377) ^ 2135816 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1945728377) ^ 7288 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_2280632647 : Nat.Prime 2280632647 := by
  apply lucas_primality 2280632647 (3 : ZMod 2280632647)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (241, 1), (1577201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (241, 1), (1577201, 1)] : List FactorBlock).map factorBlockValue).prod) = 2280632647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_241
      · exact prime_eightyFourCD_1577201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2280632647) ^ 1140316323 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2280632647) ^ 760210882 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2280632647) ^ 9463206 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2280632647) ^ 1446 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_2336019263 : Nat.Prime 2336019263 := by
  apply lucas_primality 2336019263 (5 : ZMod 2336019263)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4583, 1), (254857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4583, 1), (254857, 1)] : List FactorBlock).map factorBlockValue).prod) = 2336019263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_4583
      · exact prime_eightyFourCD_254857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2336019263) ^ 1168009631 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2336019263) ^ 509714 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2336019263) ^ 9166 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_2479781987 : Nat.Prime 2479781987 := by
  apply lucas_primality 2479781987 (2 : ZMod 2479781987)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (443, 1), (23131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (443, 1), (23131, 1)] : List FactorBlock).map factorBlockValue).prod) = 2479781987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_443
      · exact prime_eightyFourCD_23131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2479781987) ^ 1239890993 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2479781987) ^ 225434726 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2479781987) ^ 5597702 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2479781987) ^ 107206 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_2558910217 : Nat.Prime 2558910217 := by
  apply lucas_primality 2558910217 (5 : ZMod 2558910217)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (313, 1), (340643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (313, 1), (340643, 1)] : List FactorBlock).map factorBlockValue).prod) = 2558910217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_313
      · exact prime_eightyFourCD_340643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2558910217) ^ 1279455108 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2558910217) ^ 852970072 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2558910217) ^ 8175432 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2558910217) ^ 7512 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_2567892659 : Nat.Prime 2567892659 := by
  apply lucas_primality 2567892659 (2 : ZMod 2567892659)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (27318007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (27318007, 1)] : List FactorBlock).map factorBlockValue).prod) = 2567892659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_47
      · exact prime_eightyFourCD_27318007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2567892659) ^ 1283946329 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2567892659) ^ 54636014 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2567892659) ^ 94 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_2824949003 : Nat.Prime 2824949003 := by
  apply lucas_primality 2824949003 (2 : ZMod 2824949003)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (7890919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (7890919, 1)] : List FactorBlock).map factorBlockValue).prod) = 2824949003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_179
      · exact prime_eightyFourCD_7890919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2824949003) ^ 1412474501 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2824949003) ^ 15781838 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2824949003) ^ 358 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_2897084683 : Nat.Prime 2897084683 := by
  apply lucas_primality 2897084683 (3 : ZMod 2897084683)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (37, 1), (41, 1), (79, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (37, 1), (41, 1), (79, 2)] : List FactorBlock).map factorBlockValue).prod) = 2897084683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_17
      · exact prime_eightyFourCD_37
      · exact prime_eightyFourCD_41
      · exact prime_eightyFourCD_79
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2897084683) ^ 1448542341 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2897084683) ^ 965694894 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2897084683) ^ 170416746 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2897084683) ^ 78299586 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2897084683) ^ 70660602 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2897084683) ^ 36671958 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_2908561687 : Nat.Prime 2908561687 := by
  apply lucas_primality 2908561687 (6 : ZMod 2908561687)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (443, 1), (57593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (443, 1), (57593, 1)] : List FactorBlock).map factorBlockValue).prod) = 2908561687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_19
      · exact prime_eightyFourCD_443
      · exact prime_eightyFourCD_57593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2908561687) ^ 1454280843 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2908561687) ^ 969520562 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2908561687) ^ 153082194 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2908561687) ^ 6565602 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2908561687) ^ 50502 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_3360484849 : Nat.Prime 3360484849 := by
  apply lucas_primality 3360484849 (11 : ZMod 3360484849)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (10001443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (10001443, 1)] : List FactorBlock).map factorBlockValue).prod) = 3360484849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_10001443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3360484849) ^ 1680242424 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 3360484849) ^ 1120161616 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 3360484849) ^ 480069264 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 3360484849) ^ 336 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_3507143347 : Nat.Prime 3507143347 := by
  apply lucas_primality 3507143347 (2 : ZMod 3507143347)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 2), (37, 1), (11941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 2), (37, 1), (11941, 1)] : List FactorBlock).map factorBlockValue).prod) = 3507143347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_37
      · exact prime_eightyFourCD_11941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3507143347) ^ 1753571673 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3507143347) ^ 1169047782 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3507143347) ^ 501020478 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3507143347) ^ 94787658 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3507143347) ^ 293706 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_3540544289 : Nat.Prime 3540544289 := by
  apply lucas_primality 3540544289 (3 : ZMod 3540544289)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (167, 1), (662527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (167, 1), (662527, 1)] : List FactorBlock).map factorBlockValue).prod) = 3540544289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_167
      · exact prime_eightyFourCD_662527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3540544289) ^ 1770272144 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3540544289) ^ 21200864 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3540544289) ^ 5344 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_3756770741 : Nat.Prime 3756770741 := by
  apply lucas_primality 3756770741 (7 : ZMod 3756770741)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (79, 1), (2377703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (79, 1), (2377703, 1)] : List FactorBlock).map factorBlockValue).prod) = 3756770741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_79
      · exact prime_eightyFourCD_2377703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3756770741) ^ 1878385370 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3756770741) ^ 751354148 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3756770741) ^ 47554060 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3756770741) ^ 1580 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_3863079383 : Nat.Prime 3863079383 := by
  apply lucas_primality 3863079383 (5 : ZMod 3863079383)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 2), (99971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 2), (99971, 1)] : List FactorBlock).map factorBlockValue).prod) = 3863079383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_139
      · exact prime_eightyFourCD_99971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3863079383) ^ 1931539691 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3863079383) ^ 27791938 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3863079383) ^ 38642 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_4324929107 : Nat.Prime 4324929107 := by
  apply lucas_primality 4324929107 (2 : ZMod 4324929107)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (131, 1), (170179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (131, 1), (170179, 1)] : List FactorBlock).map factorBlockValue).prod) = 4324929107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_97
      · exact prime_eightyFourCD_131
      · exact prime_eightyFourCD_170179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4324929107) ^ 2162464553 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4324929107) ^ 44586898 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4324929107) ^ 33014726 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4324929107) ^ 25414 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_4491548717 : Nat.Prime 4491548717 := by
  apply lucas_primality 4491548717 (2 : ZMod 4491548717)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (263, 1), (251149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (263, 1), (251149, 1)] : List FactorBlock).map factorBlockValue).prod) = 4491548717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_17
      · exact prime_eightyFourCD_263
      · exact prime_eightyFourCD_251149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4491548717) ^ 2245774358 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4491548717) ^ 264208748 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4491548717) ^ 17078132 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4491548717) ^ 17884 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_5059861831 : Nat.Prime 5059861831 := by
  apply lucas_primality 5059861831 (3 : ZMod 5059861831)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (59, 1), (239, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (59, 1), (239, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) = 5059861831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_59
      · exact prime_eightyFourCD_239
      · exact prime_eightyFourCD_443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5059861831) ^ 2529930915 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5059861831) ^ 1686620610 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5059861831) ^ 1011972366 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5059861831) ^ 85760370 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5059861831) ^ 21170970 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5059861831) ^ 11421810 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_5381738903 : Nat.Prime 5381738903 := by
  apply lucas_primality 5381738903 (5 : ZMod 5381738903)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (313, 1), (8597027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (313, 1), (8597027, 1)] : List FactorBlock).map factorBlockValue).prod) = 5381738903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_313
      · exact prime_eightyFourCD_8597027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5381738903) ^ 2690869451 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 5381738903) ^ 17194054 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 5381738903) ^ 626 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_5499760961 : Nat.Prime 5499760961 := by
  apply lucas_primality 5499760961 (6 : ZMod 5499760961)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (191, 1), (89983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (191, 1), (89983, 1)] : List FactorBlock).map factorBlockValue).prod) = 5499760961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_191
      · exact prime_eightyFourCD_89983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5499760961) ^ 2749880480 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 5499760961) ^ 1099952192 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 5499760961) ^ 28794560 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 5499760961) ^ 61120 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_6041178673 : Nat.Prime 6041178673 := by
  apply lucas_primality 6041178673 (5 : ZMod 6041178673)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (127, 1), (409, 1), (2423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (127, 1), (409, 1), (2423, 1)] : List FactorBlock).map factorBlockValue).prod) = 6041178673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_127
      · exact prime_eightyFourCD_409
      · exact prime_eightyFourCD_2423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6041178673) ^ 3020589336 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 6041178673) ^ 2013726224 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 6041178673) ^ 47568336 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 6041178673) ^ 14770608 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 6041178673) ^ 2493264 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_6128287609 : Nat.Prime 6128287609 := by
  apply lucas_primality 6128287609 (7 : ZMod 6128287609)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1669, 1), (152993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1669, 1), (152993, 1)] : List FactorBlock).map factorBlockValue).prod) = 6128287609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_1669
      · exact prime_eightyFourCD_152993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6128287609) ^ 3064143804 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 6128287609) ^ 2042762536 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 6128287609) ^ 3671832 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 6128287609) ^ 40056 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_7412773091 : Nat.Prime 7412773091 := by
  apply lucas_primality 7412773091 (2 : ZMod 7412773091)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (8191, 1), (90499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (8191, 1), (90499, 1)] : List FactorBlock).map factorBlockValue).prod) = 7412773091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_8191
      · exact prime_eightyFourCD_90499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7412773091) ^ 3706386545 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7412773091) ^ 1482554618 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7412773091) ^ 904990 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7412773091) ^ 81910 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_7482966307 : Nat.Prime 7482966307 := by
  apply lucas_primality 7482966307 (3 : ZMod 7482966307)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1247161051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1247161051, 1)] : List FactorBlock).map factorBlockValue).prod) = 7482966307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_1247161051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7482966307) ^ 3741483153 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 7482966307) ^ 2494322102 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 7482966307) ^ 6 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_7567118021 : Nat.Prime 7567118021 := by
  apply lucas_primality 7567118021 (2 : ZMod 7567118021)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (11, 1), (67, 1), (10477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (11, 1), (67, 1), (10477, 1)] : List FactorBlock).map factorBlockValue).prod) = 7567118021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_67
      · exact prime_eightyFourCD_10477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7567118021) ^ 3783559010 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7567118021) ^ 1513423604 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7567118021) ^ 1081016860 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7567118021) ^ 687919820 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7567118021) ^ 112942060 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7567118021) ^ 722260 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_7751915827 : Nat.Prime 7751915827 := by
  apply lucas_primality 7751915827 (2 : ZMod 7751915827)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (173, 1), (76991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (173, 1), (76991, 1)] : List FactorBlock).map factorBlockValue).prod) = 7751915827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_97
      · exact prime_eightyFourCD_173
      · exact prime_eightyFourCD_76991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7751915827) ^ 3875957913 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7751915827) ^ 2583971942 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7751915827) ^ 79916658 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7751915827) ^ 44808762 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7751915827) ^ 100686 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_7920470477 : Nat.Prime 7920470477 := by
  apply lucas_primality 7920470477 (2 : ZMod 7920470477)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (8693, 1), (13399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (8693, 1), (13399, 1)] : List FactorBlock).map factorBlockValue).prod) = 7920470477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_17
      · exact prime_eightyFourCD_8693
      · exact prime_eightyFourCD_13399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7920470477) ^ 3960235238 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7920470477) ^ 465910028 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7920470477) ^ 911132 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7920470477) ^ 591124 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_8792546663 : Nat.Prime 8792546663 := by
  apply lucas_primality 8792546663 (5 : ZMod 8792546663)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13577, 1), (323803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13577, 1), (323803, 1)] : List FactorBlock).map factorBlockValue).prod) = 8792546663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_13577
      · exact prime_eightyFourCD_323803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8792546663) ^ 4396273331 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 8792546663) ^ 647606 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 8792546663) ^ 27154 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_10013723393 : Nat.Prime 10013723393 := by
  apply lucas_primality 10013723393 (3 : ZMod 10013723393)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (39116107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (39116107, 1)] : List FactorBlock).map factorBlockValue).prod) = 10013723393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_39116107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 10013723393) ^ 5006861696 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 10013723393) ^ 256 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_11634246749 : Nat.Prime 11634246749 := by
  apply lucas_primality 11634246749 (2 : ZMod 11634246749)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2908561687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2908561687, 1)] : List FactorBlock).map factorBlockValue).prod) = 11634246749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_2908561687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 11634246749) ^ 5817123374 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 11634246749) ^ 4 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_11802392531 : Nat.Prime 11802392531 := by
  apply lucas_primality 11802392531 (2 : ZMod 11802392531)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (619, 1), (26119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (619, 1), (26119, 1)] : List FactorBlock).map factorBlockValue).prod) = 11802392531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_73
      · exact prime_eightyFourCD_619
      · exact prime_eightyFourCD_26119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11802392531) ^ 5901196265 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 11802392531) ^ 2360478506 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 11802392531) ^ 161676610 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 11802392531) ^ 19066870 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 11802392531) ^ 451870 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_12985300303 : Nat.Prime 12985300303 := by
  apply lucas_primality 12985300303 (3 : ZMod 12985300303)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19, 1), (23, 1), (380957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19, 1), (23, 1), (380957, 1)] : List FactorBlock).map factorBlockValue).prod) = 12985300303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_19
      · exact prime_eightyFourCD_23
      · exact prime_eightyFourCD_380957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12985300303) ^ 6492650151 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 12985300303) ^ 4328433434 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 12985300303) ^ 998869254 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 12985300303) ^ 683436858 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 12985300303) ^ 564578274 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 12985300303) ^ 34086 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_14727527099 : Nat.Prime 14727527099 := by
  apply lucas_primality 14727527099 (2 : ZMod 14727527099)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (41, 1), (227, 1), (27283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (41, 1), (227, 1), (27283, 1)] : List FactorBlock).map factorBlockValue).prod) = 14727527099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_29
      · exact prime_eightyFourCD_41
      · exact prime_eightyFourCD_227
      · exact prime_eightyFourCD_27283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14727527099) ^ 7363763549 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 14727527099) ^ 507845762 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 14727527099) ^ 359207978 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 14727527099) ^ 64878974 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 14727527099) ^ 539806 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_16949694019 : Nat.Prime 16949694019 := by
  apply lucas_primality 16949694019 (2 : ZMod 16949694019)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2824949003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2824949003, 1)] : List FactorBlock).map factorBlockValue).prod) = 16949694019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_2824949003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16949694019) ^ 8474847009 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16949694019) ^ 5649898006 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16949694019) ^ 6 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_17002228027 : Nat.Prime 17002228027 := by
  apply lucas_primality 17002228027 (2 : ZMod 17002228027)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (293, 1), (1381621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (293, 1), (1381621, 1)] : List FactorBlock).map factorBlockValue).prod) = 17002228027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_293
      · exact prime_eightyFourCD_1381621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17002228027) ^ 8501114013 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17002228027) ^ 5667409342 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17002228027) ^ 2428889718 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17002228027) ^ 58028082 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17002228027) ^ 12306 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_17712609709 : Nat.Prime 17712609709 := by
  apply lucas_primality 17712609709 (2 : ZMod 17712609709)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (2749, 1), (12487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (2749, 1), (12487, 1)] : List FactorBlock).map factorBlockValue).prod) = 17712609709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_43
      · exact prime_eightyFourCD_2749
      · exact prime_eightyFourCD_12487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17712609709) ^ 8856304854 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17712609709) ^ 5904203236 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17712609709) ^ 411921156 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17712609709) ^ 6443292 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17712609709) ^ 1418484 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_18536890189 : Nat.Prime 18536890189 := by
  apply lucas_primality 18536890189 (7 : ZMod 18536890189)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (113, 1), (3109, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (113, 1), (3109, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) = 18536890189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_113
      · exact prime_eightyFourCD_3109
      · exact prime_eightyFourCD_4397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 18536890189) ^ 9268445094 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 18536890189) ^ 6178963396 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 18536890189) ^ 164043276 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 18536890189) ^ 5962332 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 18536890189) ^ 4215804 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_20504724677 : Nat.Prime 20504724677 := by
  apply lucas_primality 20504724677 (2 : ZMod 20504724677)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (41, 1), (101, 1), (33457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (41, 1), (101, 1), (33457, 1)] : List FactorBlock).map factorBlockValue).prod) = 20504724677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_37
      · exact prime_eightyFourCD_41
      · exact prime_eightyFourCD_101
      · exact prime_eightyFourCD_33457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20504724677) ^ 10252362338 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 20504724677) ^ 554181748 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 20504724677) ^ 500115236 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 20504724677) ^ 203017076 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 20504724677) ^ 612868 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_20674148129 : Nat.Prime 20674148129 := by
  apply lucas_primality 20674148129 (3 : ZMod 20674148129)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (149, 1), (491, 1), (8831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (149, 1), (491, 1), (8831, 1)] : List FactorBlock).map factorBlockValue).prod) = 20674148129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_149
      · exact prime_eightyFourCD_491
      · exact prime_eightyFourCD_8831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 20674148129) ^ 10337074064 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 20674148129) ^ 138752672 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 20674148129) ^ 42106208 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 20674148129) ^ 2341088 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_23060753531 : Nat.Prime 23060753531 := by
  apply lucas_primality 23060753531 (6 : ZMod 23060753531)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (5441, 1), (22307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (5441, 1), (22307, 1)] : List FactorBlock).map factorBlockValue).prod) = 23060753531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_19
      · exact prime_eightyFourCD_5441
      · exact prime_eightyFourCD_22307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 23060753531) ^ 11530376765 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 23060753531) ^ 4612150706 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 23060753531) ^ 1213723870 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 23060753531) ^ 4238330 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 23060753531) ^ 1033790 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_30326687849 : Nat.Prime 30326687849 := by
  apply lucas_primality 30326687849 (3 : ZMod 30326687849)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (421, 1), (9004361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (421, 1), (9004361, 1)] : List FactorBlock).map factorBlockValue).prod) = 30326687849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_421
      · exact prime_eightyFourCD_9004361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 30326687849) ^ 15163343924 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 30326687849) ^ 72034888 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 30326687849) ^ 3368 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_34669136773 : Nat.Prime 34669136773 := by
  apply lucas_primality 34669136773 (2 : ZMod 34669136773)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (499, 1), (1929923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (499, 1), (1929923, 1)] : List FactorBlock).map factorBlockValue).prod) = 34669136773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_499
      · exact prime_eightyFourCD_1929923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34669136773) ^ 17334568386 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 34669136773) ^ 11556378924 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 34669136773) ^ 69477228 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 34669136773) ^ 17964 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_40460709349 : Nat.Prime 40460709349 := by
  apply lucas_primality 40460709349 (6 : ZMod 40460709349)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (23, 1), (48865591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (23, 1), (48865591, 1)] : List FactorBlock).map factorBlockValue).prod) = 40460709349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_23
      · exact prime_eightyFourCD_48865591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 40460709349) ^ 20230354674 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 40460709349) ^ 13486903116 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 40460709349) ^ 1759161276 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 40460709349) ^ 828 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_45081248893 : Nat.Prime 45081248893 := by
  apply lucas_primality 45081248893 (11 : ZMod 45081248893)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3756770741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3756770741, 1)] : List FactorBlock).map factorBlockValue).prod) = 45081248893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_3756770741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 45081248893) ^ 22540624446 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 45081248893) ^ 15027082964 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 45081248893) ^ 12 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_46905158617 : Nat.Prime 46905158617 := by
  apply lucas_primality 46905158617 (15 : ZMod 46905158617)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1229, 1), (1590221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1229, 1), (1590221, 1)] : List FactorBlock).map factorBlockValue).prod) = 46905158617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_1229
      · exact prime_eightyFourCD_1590221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 46905158617) ^ 23452579308 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (15 : ZMod 46905158617) ^ 15635052872 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (15 : ZMod 46905158617) ^ 38165304 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (15 : ZMod 46905158617) ^ 29496 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_51357853181 : Nat.Prime 51357853181 := by
  apply lucas_primality 51357853181 (2 : ZMod 51357853181)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2567892659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2567892659, 1)] : List FactorBlock).map factorBlockValue).prod) = 51357853181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_2567892659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 51357853181) ^ 25678926590 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 51357853181) ^ 10271570636 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 51357853181) ^ 20 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_60718341973 : Nat.Prime 60718341973 := by
  apply lucas_primality 60718341973 (2 : ZMod 60718341973)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5059861831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5059861831, 1)] : List FactorBlock).map factorBlockValue).prod) = 60718341973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5059861831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 60718341973) ^ 30359170986 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 60718341973) ^ 20239447324 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 60718341973) ^ 12 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_61592819909 : Nat.Prime 61592819909 := by
  apply lucas_primality 61592819909 (2 : ZMod 61592819909)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1291, 1), (11927347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1291, 1), (11927347, 1)] : List FactorBlock).map factorBlockValue).prod) = 61592819909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_1291
      · exact prime_eightyFourCD_11927347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 61592819909) ^ 30796409954 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 61592819909) ^ 47709388 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 61592819909) ^ 5164 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_61817999393 : Nat.Prime 61817999393 := by
  apply lucas_primality 61817999393 (3 : ZMod 61817999393)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (23, 1), (83991847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (23, 1), (83991847, 1)] : List FactorBlock).map factorBlockValue).prod) = 61817999393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_23
      · exact prime_eightyFourCD_83991847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 61817999393) ^ 30908999696 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 61817999393) ^ 2687739104 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 61817999393) ^ 736 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_74697500399 : Nat.Prime 74697500399 := by
  apply lucas_primality 74697500399 (7 : ZMod 74697500399)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (93169, 1), (400871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (93169, 1), (400871, 1)] : List FactorBlock).map factorBlockValue).prod) = 74697500399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_93169
      · exact prime_eightyFourCD_400871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 74697500399) ^ 37348750199 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 74697500399) ^ 801742 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 74697500399) ^ 186338 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_88911631663 : Nat.Prime 88911631663 := by
  apply lucas_primality 88911631663 (3 : ZMod 88911631663)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (41, 1), (51632771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (41, 1), (51632771, 1)] : List FactorBlock).map factorBlockValue).prod) = 88911631663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_41
      · exact prime_eightyFourCD_51632771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88911631663) ^ 44455815831 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 88911631663) ^ 29637210554 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 88911631663) ^ 12701661666 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 88911631663) ^ 2168576382 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 88911631663) ^ 1722 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_92181738809 : Nat.Prime 92181738809 := by
  apply lucas_primality 92181738809 (3 : ZMod 92181738809)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (5381, 1), (125963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (5381, 1), (125963, 1)] : List FactorBlock).map factorBlockValue).prod) = 92181738809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_17
      · exact prime_eightyFourCD_5381
      · exact prime_eightyFourCD_125963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 92181738809) ^ 46090869404 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 92181738809) ^ 5422455224 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 92181738809) ^ 17130968 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 92181738809) ^ 731816 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_96108461129 : Nat.Prime 96108461129 := by
  apply lucas_primality 96108461129 (3 : ZMod 96108461129)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (271, 1), (1081231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (271, 1), (1081231, 1)] : List FactorBlock).map factorBlockValue).prod) = 96108461129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_41
      · exact prime_eightyFourCD_271
      · exact prime_eightyFourCD_1081231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 96108461129) ^ 48054230564 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 96108461129) ^ 2344108808 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 96108461129) ^ 354643768 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 96108461129) ^ 88888 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_104072517847 : Nat.Prime 104072517847 := by
  apply lucas_primality 104072517847 (3 : ZMod 104072517847)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (175206259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (175206259, 1)] : List FactorBlock).map factorBlockValue).prod) = 104072517847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_175206259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 104072517847) ^ 52036258923 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 104072517847) ^ 34690839282 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 104072517847) ^ 9461137986 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 104072517847) ^ 594 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_108780897713 : Nat.Prime 108780897713 := by
  apply lucas_primality 108780897713 (3 : ZMod 108780897713)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (7129, 1), (56099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (7129, 1), (56099, 1)] : List FactorBlock).map factorBlockValue).prod) = 108780897713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_17
      · exact prime_eightyFourCD_7129
      · exact prime_eightyFourCD_56099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 108780897713) ^ 54390448856 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 108780897713) ^ 6398876336 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 108780897713) ^ 15258928 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 108780897713) ^ 1939088 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_108973134937 : Nat.Prime 108973134937 := by
  apply lucas_primality 108973134937 (10 : ZMod 108973134937)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (17, 1), (43, 1), (2070473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (17, 1), (43, 1), (2070473, 1)] : List FactorBlock).map factorBlockValue).prod) = 108973134937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_17
      · exact prime_eightyFourCD_43
      · exact prime_eightyFourCD_2070473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 108973134937) ^ 54486567468 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 108973134937) ^ 36324378312 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 108973134937) ^ 6410184408 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 108973134937) ^ 2534258952 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 108973134937) ^ 52632 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_121654248977 : Nat.Prime 121654248977 := by
  apply lucas_primality 121654248977 (5 : ZMod 121654248977)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (1709, 1), (342233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (1709, 1), (342233, 1)] : List FactorBlock).map factorBlockValue).prod) = 121654248977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_1709
      · exact prime_eightyFourCD_342233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 121654248977) ^ 60827124488 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 121654248977) ^ 9358019152 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 121654248977) ^ 71184464 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 121654248977) ^ 355472 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_138364521187 : Nat.Prime 138364521187 := by
  apply lucas_primality 138364521187 (3 : ZMod 138364521187)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23060753531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23060753531, 1)] : List FactorBlock).map factorBlockValue).prod) = 138364521187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_23060753531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 138364521187) ^ 69182260593 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 138364521187) ^ 46121507062 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 138364521187) ^ 6 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_150089141863 : Nat.Prime 150089141863 := by
  apply lucas_primality 150089141863 (5 : ZMod 150089141863)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (83, 1), (173, 1), (17597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (83, 1), (173, 1), (17597, 1)] : List FactorBlock).map factorBlockValue).prod) = 150089141863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_83
      · exact prime_eightyFourCD_173
      · exact prime_eightyFourCD_17597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 150089141863) ^ 75044570931 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 150089141863) ^ 50029713954 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 150089141863) ^ 13644467442 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 150089141863) ^ 1808302914 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 150089141863) ^ 867567294 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 150089141863) ^ 8529246 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_162593128717 : Nat.Prime 162593128717 := by
  apply lucas_primality 162593128717 (5 : ZMod 162593128717)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (437078303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (437078303, 1)] : List FactorBlock).map factorBlockValue).prod) = 162593128717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_31
      · exact prime_eightyFourCD_437078303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 162593128717) ^ 81296564358 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 162593128717) ^ 54197709572 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 162593128717) ^ 5244939636 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 162593128717) ^ 372 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_166188667663 : Nat.Prime 166188667663 := by
  apply lucas_primality 166188667663 (3 : ZMod 166188667663)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (113, 1), (81705343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (113, 1), (81705343, 1)] : List FactorBlock).map factorBlockValue).prod) = 166188667663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_113
      · exact prime_eightyFourCD_81705343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 166188667663) ^ 83094333831 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 166188667663) ^ 55396222554 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 166188667663) ^ 1470696174 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 166188667663) ^ 2034 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_179512272943 : Nat.Prime 179512272943 := by
  apply lucas_primality 179512272943 (3 : ZMod 179512272943)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (965119747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (965119747, 1)] : List FactorBlock).map factorBlockValue).prod) = 179512272943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_31
      · exact prime_eightyFourCD_965119747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 179512272943) ^ 89756136471 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 179512272943) ^ 59837424314 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 179512272943) ^ 5790718482 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 179512272943) ^ 186 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_184363477619 : Nat.Prime 184363477619 := by
  apply lucas_primality 184363477619 (2 : ZMod 184363477619)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (92181738809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (92181738809, 1)] : List FactorBlock).map factorBlockValue).prod) = 184363477619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_92181738809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 184363477619) ^ 92181738809 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 184363477619) ^ 2 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_211021119913 : Nat.Prime 211021119913 := by
  apply lucas_primality 211021119913 (10 : ZMod 211021119913)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (8792546663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (8792546663, 1)] : List FactorBlock).map factorBlockValue).prod) = 211021119913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_8792546663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 211021119913) ^ 105510559956 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 211021119913) ^ 70340373304 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 211021119913) ^ 24 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_217561795427 : Nat.Prime 217561795427 := by
  apply lucas_primality 217561795427 (2 : ZMod 217561795427)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (108780897713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (108780897713, 1)] : List FactorBlock).map factorBlockValue).prod) = 217561795427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_108780897713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 217561795427) ^ 108780897713 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 217561795427) ^ 2 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_226398713377 : Nat.Prime 226398713377 := by
  apply lucas_primality 226398713377 (5 : ZMod 226398713377)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (214392721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (214392721, 1)] : List FactorBlock).map factorBlockValue).prod) = 226398713377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_214392721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 226398713377) ^ 113199356688 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 226398713377) ^ 75466237792 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 226398713377) ^ 20581701216 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 226398713377) ^ 1056 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_257635509959 : Nat.Prime 257635509959 := by
  apply lucas_primality 257635509959 (7 : ZMod 257635509959)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (29, 1), (233789029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (29, 1), (233789029, 1)] : List FactorBlock).map factorBlockValue).prod) = 257635509959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_19
      · exact prime_eightyFourCD_29
      · exact prime_eightyFourCD_233789029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 257635509959) ^ 128817754979 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 257635509959) ^ 13559763682 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 257635509959) ^ 8883983102 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 257635509959) ^ 1102 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_295488826819 : Nat.Prime 295488826819 := by
  apply lucas_primality 295488826819 (2 : ZMod 295488826819)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1783, 1), (27620941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1783, 1), (27620941, 1)] : List FactorBlock).map factorBlockValue).prod) = 295488826819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_1783
      · exact prime_eightyFourCD_27620941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 295488826819) ^ 147744413409 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 295488826819) ^ 98496275606 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 295488826819) ^ 165725646 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 295488826819) ^ 10698 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_335885211953 : Nat.Prime 335885211953 := by
  apply lucas_primality 335885211953 (3 : ZMod 335885211953)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (113, 1), (6406111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (113, 1), (6406111, 1)] : List FactorBlock).map factorBlockValue).prod) = 335885211953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_29
      · exact prime_eightyFourCD_113
      · exact prime_eightyFourCD_6406111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 335885211953) ^ 167942605976 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 335885211953) ^ 11582248688 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 335885211953) ^ 2972435504 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 335885211953) ^ 52432 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_416290071389 : Nat.Prime 416290071389 := by
  apply lucas_primality 416290071389 (2 : ZMod 416290071389)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (104072517847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (104072517847, 1)] : List FactorBlock).map factorBlockValue).prod) = 416290071389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_104072517847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 416290071389) ^ 208145035694 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 416290071389) ^ 4 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_440823010189 : Nat.Prime 440823010189 := by
  apply lucas_primality 440823010189 (6 : ZMod 440823010189)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (937, 1), (1277, 1), (2791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (937, 1), (1277, 1), (2791, 1)] : List FactorBlock).map factorBlockValue).prod) = 440823010189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_937
      · exact prime_eightyFourCD_1277
      · exact prime_eightyFourCD_2791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 440823010189) ^ 220411505094 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 440823010189) ^ 146941003396 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 440823010189) ^ 40074819108 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 440823010189) ^ 470462124 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 440823010189) ^ 345202044 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 440823010189) ^ 157944468 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_459038483489 : Nat.Prime 459038483489 := by
  apply lucas_primality 459038483489 (3 : ZMod 459038483489)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (1103457893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (1103457893, 1)] : List FactorBlock).map factorBlockValue).prod) = 459038483489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_1103457893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 459038483489) ^ 229519241744 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 459038483489) ^ 35310652576 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 459038483489) ^ 416 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_789644411711 : Nat.Prime 789644411711 := by
  apply lucas_primality 789644411711 (11 : ZMod 789644411711)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (47, 1), (379, 1), (57571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (47, 1), (379, 1), (57571, 1)] : List FactorBlock).map factorBlockValue).prod) = 789644411711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_47
      · exact prime_eightyFourCD_379
      · exact prime_eightyFourCD_57571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 789644411711) ^ 394822205855 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 789644411711) ^ 157928882342 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 789644411711) ^ 112806344530 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 789644411711) ^ 71785855610 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 789644411711) ^ 16800944930 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 789644411711) ^ 2083494490 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 789644411711) ^ 13716010 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_950611790207 : Nat.Prime 950611790207 := by
  apply lucas_primality 950611790207 (5 : ZMod 950611790207)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1901, 1), (19233031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1901, 1), (19233031, 1)] : List FactorBlock).map factorBlockValue).prod) = 950611790207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_1901
      · exact prime_eightyFourCD_19233031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 950611790207) ^ 475305895103 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 950611790207) ^ 73123983862 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 950611790207) ^ 500058806 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 950611790207) ^ 49426 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1122147049783 : Nat.Prime 1122147049783 := by
  apply lucas_primality 1122147049783 (5 : ZMod 1122147049783)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17002228027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17002228027, 1)] : List FactorBlock).map factorBlockValue).prod) = 1122147049783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_17002228027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1122147049783) ^ 561073524891 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1122147049783) ^ 374049016594 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1122147049783) ^ 102013368162 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1122147049783) ^ 66 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1358392280263 : Nat.Prime 1358392280263 := by
  apply lucas_primality 1358392280263 (5 : ZMod 1358392280263)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (226398713377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (226398713377, 1)] : List FactorBlock).map factorBlockValue).prod) = 1358392280263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_226398713377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1358392280263) ^ 679196140131 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1358392280263) ^ 452797426754 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1358392280263) ^ 6 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1370602112707 : Nat.Prime 1370602112707 := by
  apply lucas_primality 1370602112707 (3 : ZMod 1370602112707)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (139, 1), (547802603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (139, 1), (547802603, 1)] : List FactorBlock).map factorBlockValue).prod) = 1370602112707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_139
      · exact prime_eightyFourCD_547802603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1370602112707) ^ 685301056353 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1370602112707) ^ 456867370902 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1370602112707) ^ 9860446854 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1370602112707) ^ 2502 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1532436778823 : Nat.Prime 1532436778823 := by
  apply lucas_primality 1532436778823 (5 : ZMod 1532436778823)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1307, 1), (586242073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1307, 1), (586242073, 1)] : List FactorBlock).map factorBlockValue).prod) = 1532436778823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_1307
      · exact prime_eightyFourCD_586242073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1532436778823) ^ 766218389411 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1532436778823) ^ 1172484146 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1532436778823) ^ 2614 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1772146011871 : Nat.Prime 1772146011871 := by
  apply lucas_primality 1772146011871 (7 : ZMod 1772146011871)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 1), (19, 1), (2281, 1), (34949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 1), (19, 1), (2281, 1), (34949, 1)] : List FactorBlock).map factorBlockValue).prod) = 1772146011871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_19
      · exact prime_eightyFourCD_2281
      · exact prime_eightyFourCD_34949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1772146011871) ^ 886073005935 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1772146011871) ^ 590715337290 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1772146011871) ^ 354429202374 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1772146011871) ^ 136318923990 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1772146011871) ^ 93270842730 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1772146011871) ^ 776916270 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1772146011871) ^ 50706630 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1950157879457 : Nat.Prime 1950157879457 := by
  apply lucas_primality 1950157879457 (3 : ZMod 1950157879457)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (101, 1), (10627, 1), (56779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (101, 1), (10627, 1), (56779, 1)] : List FactorBlock).map factorBlockValue).prod) = 1950157879457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_101
      · exact prime_eightyFourCD_10627
      · exact prime_eightyFourCD_56779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1950157879457) ^ 975078939728 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1950157879457) ^ 19308493856 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1950157879457) ^ 183509728 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1950157879457) ^ 34346464 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1991583150407 : Nat.Prime 1991583150407 := by
  apply lucas_primality 1991583150407 (5 : ZMod 1991583150407)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (255209, 1), (3901867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (255209, 1), (3901867, 1)] : List FactorBlock).map factorBlockValue).prod) = 1991583150407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_255209
      · exact prime_eightyFourCD_3901867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1991583150407) ^ 995791575203 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1991583150407) ^ 7803734 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1991583150407) ^ 510418 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_2930224182607 : Nat.Prime 2930224182607 := by
  apply lucas_primality 2930224182607 (5 : ZMod 2930224182607)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (7751915827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (7751915827, 1)] : List FactorBlock).map factorBlockValue).prod) = 2930224182607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_7751915827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2930224182607) ^ 1465112091303 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2930224182607) ^ 976741394202 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2930224182607) ^ 418603454658 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2930224182607) ^ 378 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_3016462917551 : Nat.Prime 3016462917551 := by
  apply lucas_primality 3016462917551 (13 : ZMod 3016462917551)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 2), (208751759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 2), (208751759, 1)] : List FactorBlock).map factorBlockValue).prod) = 3016462917551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_17
      · exact prime_eightyFourCD_208751759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 3016462917551) ^ 1508231458775 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3016462917551) ^ 603292583510 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3016462917551) ^ 177438995150 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3016462917551) ^ 14450 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_3432672507533 : Nat.Prime 3432672507533 := by
  apply lucas_primality 3432672507533 (2 : ZMod 3432672507533)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (10181, 1), (2278139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (10181, 1), (2278139, 1)] : List FactorBlock).map factorBlockValue).prod) = 3432672507533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_37
      · exact prime_eightyFourCD_10181
      · exact prime_eightyFourCD_2278139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3432672507533) ^ 1716336253766 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3432672507533) ^ 92774932636 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3432672507533) ^ 337164572 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3432672507533) ^ 1506788 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_3474109568161 : Nat.Prime 3474109568161 := by
  apply lucas_primality 3474109568161 (13 : ZMod 3474109568161)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (7, 1), (11, 1), (2879, 1), (10883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (7, 1), (11, 1), (2879, 1), (10883, 1)] : List FactorBlock).map factorBlockValue).prod) = 3474109568161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_2879
      · exact prime_eightyFourCD_10883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3474109568161) ^ 1737054784080 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3474109568161) ^ 1158036522720 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3474109568161) ^ 694821913632 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3474109568161) ^ 496301366880 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3474109568161) ^ 315828142560 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3474109568161) ^ 1206707040 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3474109568161) ^ 319223520 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_4199192066903 : Nat.Prime 4199192066903 := by
  apply lucas_primality 4199192066903 (5 : ZMod 4199192066903)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (157, 1), (1910460449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (157, 1), (1910460449, 1)] : List FactorBlock).map factorBlockValue).prod) = 4199192066903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_157
      · exact prime_eightyFourCD_1910460449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4199192066903) ^ 2099596033451 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 4199192066903) ^ 599884580986 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 4199192066903) ^ 26746446286 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 4199192066903) ^ 2198 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_4972427659889 : Nat.Prime 4972427659889 := by
  apply lucas_primality 4972427659889 (3 : ZMod 4972427659889)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (85199, 1), (280589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (85199, 1), (280589, 1)] : List FactorBlock).map factorBlockValue).prod) = 4972427659889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_85199
      · exact prime_eightyFourCD_280589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4972427659889) ^ 2486213829944 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4972427659889) ^ 382494435376 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4972427659889) ^ 58362512 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4972427659889) ^ 17721392 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_5433569121053 : Nat.Prime 5433569121053 := by
  apply lucas_primality 5433569121053 (2 : ZMod 5433569121053)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1358392280263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1358392280263, 1)] : List FactorBlock).map factorBlockValue).prod) = 5433569121053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_1358392280263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5433569121053) ^ 2716784560526 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5433569121053) ^ 4 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_5703670741243 : Nat.Prime 5703670741243 := by
  apply lucas_primality 5703670741243 (2 : ZMod 5703670741243)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (950611790207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (950611790207, 1)] : List FactorBlock).map factorBlockValue).prod) = 5703670741243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_950611790207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5703670741243) ^ 2851835370621 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5703670741243) ^ 1901223580414 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5703670741243) ^ 6 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_5828060999447 : Nat.Prime 5828060999447 := by
  apply lucas_primality 5828060999447 (7 : ZMod 5828060999447)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (416290071389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (416290071389, 1)] : List FactorBlock).map factorBlockValue).prod) = 5828060999447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_416290071389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 5828060999447) ^ 2914030499723 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 5828060999447) ^ 832580142778 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 5828060999447) ^ 14 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_12259772705179 : Nat.Prime 12259772705179 := by
  apply lucas_primality 12259772705179 (2 : ZMod 12259772705179)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1481, 1), (9413, 1), (48857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1481, 1), (9413, 1), (48857, 1)] : List FactorBlock).map factorBlockValue).prod) = 12259772705179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_1481
      · exact prime_eightyFourCD_9413
      · exact prime_eightyFourCD_48857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12259772705179) ^ 6129886352589 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 12259772705179) ^ 4086590901726 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 12259772705179) ^ 8278036938 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 12259772705179) ^ 1302429906 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 12259772705179) ^ 250931754 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_14001454695793 : Nat.Prime 14001454695793 := by
  apply lucas_primality 14001454695793 (5 : ZMod 14001454695793)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (2113, 1), (4951, 1), (27883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (2113, 1), (4951, 1), (27883, 1)] : List FactorBlock).map factorBlockValue).prod) = 14001454695793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_2113
      · exact prime_eightyFourCD_4951
      · exact prime_eightyFourCD_27883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 14001454695793) ^ 7000727347896 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 14001454695793) ^ 4667151565264 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 14001454695793) ^ 6626339184 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 14001454695793) ^ 2828005392 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 14001454695793) ^ 502150224 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_14574367091329 : Nat.Prime 14574367091329 := by
  apply lucas_primality 14574367091329 (14 : ZMod 14574367091329)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (11, 1), (21139, 1), (163223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (11, 1), (21139, 1), (163223, 1)] : List FactorBlock).map factorBlockValue).prod) = 14574367091329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_21139
      · exact prime_eightyFourCD_163223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 14574367091329) ^ 7287183545664 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (14 : ZMod 14574367091329) ^ 4858122363776 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (14 : ZMod 14574367091329) ^ 1324942462848 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (14 : ZMod 14574367091329) ^ 689453952 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (14 : ZMod 14574367091329) ^ 89291136 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_17399281684781 : Nat.Prime 17399281684781 := by
  apply lucas_primality 17399281684781 (2 : ZMod 17399281684781)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (61, 1), (89, 1), (1061, 1), (7949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (61, 1), (89, 1), (1061, 1), (7949, 1)] : List FactorBlock).map factorBlockValue).prod) = 17399281684781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_19
      · exact prime_eightyFourCD_61
      · exact prime_eightyFourCD_89
      · exact prime_eightyFourCD_1061
      · exact prime_eightyFourCD_7949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17399281684781) ^ 8699640842390 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17399281684781) ^ 3479856336956 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17399281684781) ^ 915751667620 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17399281684781) ^ 285234125980 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17399281684781) ^ 195497547020 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17399281684781) ^ 16398945980 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17399281684781) ^ 2188864220 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_22814682964973 : Nat.Prime 22814682964973 := by
  apply lucas_primality 22814682964973 (2 : ZMod 22814682964973)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5703670741243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5703670741243, 1)] : List FactorBlock).map factorBlockValue).prod) = 22814682964973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5703670741243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 22814682964973) ^ 11407341482486 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 22814682964973) ^ 4 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_37082311193923 : Nat.Prime 37082311193923 := by
  apply lucas_primality 37082311193923 (3 : ZMod 37082311193923)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (605629, 1), (10204903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (605629, 1), (10204903, 1)] : List FactorBlock).map factorBlockValue).prod) = 37082311193923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_605629
      · exact prime_eightyFourCD_10204903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37082311193923) ^ 18541155596961 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 37082311193923) ^ 12360770397974 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 37082311193923) ^ 61229418 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 37082311193923) ^ 3633774 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_39362383717207 : Nat.Prime 39362383717207 := by
  apply lucas_primality 39362383717207 (3 : ZMod 39362383717207)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (47, 1), (1811, 1), (7006823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (47, 1), (1811, 1), (7006823, 1)] : List FactorBlock).map factorBlockValue).prod) = 39362383717207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_47
      · exact prime_eightyFourCD_1811
      · exact prime_eightyFourCD_7006823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 39362383717207) ^ 19681191858603 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 39362383717207) ^ 13120794572402 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 39362383717207) ^ 3578398519746 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 39362383717207) ^ 837497525898 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 39362383717207) ^ 21735164946 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 39362383717207) ^ 5617722 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_43729706900401 : Nat.Prime 43729706900401 := by
  apply lucas_primality 43729706900401 (19 : ZMod 43729706900401)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (29, 1), (739, 1), (1301, 1), (1307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (29, 1), (739, 1), (1301, 1), (1307, 1)] : List FactorBlock).map factorBlockValue).prod) = 43729706900401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_29
      · exact prime_eightyFourCD_739
      · exact prime_eightyFourCD_1301
      · exact prime_eightyFourCD_1307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 43729706900401) ^ 21864853450200 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (19 : ZMod 43729706900401) ^ 14576568966800 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (19 : ZMod 43729706900401) ^ 8745941380080 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (19 : ZMod 43729706900401) ^ 1507920927600 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (19 : ZMod 43729706900401) ^ 59174163600 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (19 : ZMod 43729706900401) ^ 33612380400 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (19 : ZMod 43729706900401) ^ 33458077200 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_45629365929947 : Nat.Prime 45629365929947 := by
  apply lucas_primality 45629365929947 (2 : ZMod 45629365929947)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (22814682964973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (22814682964973, 1)] : List FactorBlock).map factorBlockValue).prod) = 45629365929947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_22814682964973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 45629365929947) ^ 22814682964973 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 45629365929947) ^ 2 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_48566558456051 : Nat.Prime 48566558456051 := by
  apply lucas_primality 48566558456051 (2 : ZMod 48566558456051)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (97, 1), (10013723393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (97, 1), (10013723393, 1)] : List FactorBlock).map factorBlockValue).prod) = 48566558456051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_97
      · exact prime_eightyFourCD_10013723393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 48566558456051) ^ 24283279228025 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 48566558456051) ^ 9713311691210 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 48566558456051) ^ 500686169650 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 48566558456051) ^ 4850 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_49691749531273 : Nat.Prime 49691749531273 := by
  apply lucas_primality 49691749531273 (5 : ZMod 49691749531273)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (108973134937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (108973134937, 1)] : List FactorBlock).map factorBlockValue).prod) = 49691749531273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_19
      · exact prime_eightyFourCD_108973134937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 49691749531273) ^ 24845874765636 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 49691749531273) ^ 16563916510424 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 49691749531273) ^ 2615355238488 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 49691749531273) ^ 456 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_60264034333183 : Nat.Prime 60264034333183 := by
  apply lucas_primality 60264034333183 (3 : ZMod 60264034333183)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (137, 1), (10709, 1), (73613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (137, 1), (10709, 1), (73613, 1)] : List FactorBlock).map factorBlockValue).prod) = 60264034333183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_31
      · exact prime_eightyFourCD_137
      · exact prime_eightyFourCD_10709
      · exact prime_eightyFourCD_73613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 60264034333183) ^ 30132017166591 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 60264034333183) ^ 20088011444394 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 60264034333183) ^ 1944001107522 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 60264034333183) ^ 439883462286 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 60264034333183) ^ 5627419398 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 60264034333183) ^ 818660214 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_83394551885971 : Nat.Prime 83394551885971 := by
  apply lucas_primality 83394551885971 (7 : ZMod 83394551885971)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (443, 1), (4349, 1), (110989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (443, 1), (4349, 1), (110989, 1)] : List FactorBlock).map factorBlockValue).prod) = 83394551885971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_443
      · exact prime_eightyFourCD_4349
      · exact prime_eightyFourCD_110989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 83394551885971) ^ 41697275942985 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 83394551885971) ^ 27798183961990 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 83394551885971) ^ 16678910377194 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 83394551885971) ^ 6414965529690 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 83394551885971) ^ 188249552790 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 83394551885971) ^ 19175569530 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 83394551885971) ^ 751376730 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_110230907510639 : Nat.Prime 110230907510639 := by
  apply lucas_primality 110230907510639 (11 : ZMod 110230907510639)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (739, 1), (1264086919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (739, 1), (1264086919, 1)] : List FactorBlock).map factorBlockValue).prod) = 110230907510639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_59
      · exact prime_eightyFourCD_739
      · exact prime_eightyFourCD_1264086919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 110230907510639) ^ 55115453755319 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 110230907510639) ^ 1868320466282 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 110230907510639) ^ 149162256442 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 110230907510639) ^ 87202 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_129362004579481 : Nat.Prime 129362004579481 := by
  apply lucas_primality 129362004579481 (13 : ZMod 129362004579481)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (37, 1), (199, 1), (146409983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (37, 1), (199, 1), (146409983, 1)] : List FactorBlock).map factorBlockValue).prod) = 129362004579481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_37
      · exact prime_eightyFourCD_199
      · exact prime_eightyFourCD_146409983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 129362004579481) ^ 64681002289740 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 129362004579481) ^ 43120668193160 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 129362004579481) ^ 25872400915896 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 129362004579481) ^ 3496270394040 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 129362004579481) ^ 650060324520 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 129362004579481) ^ 883560 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_131755336656857 : Nat.Prime 131755336656857 := by
  apply lucas_primality 131755336656857 (3 : ZMod 131755336656857)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (863, 1), (1734901199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (863, 1), (1734901199, 1)] : List FactorBlock).map factorBlockValue).prod) = 131755336656857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_863
      · exact prime_eightyFourCD_1734901199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 131755336656857) ^ 65877668328428 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 131755336656857) ^ 11977757877896 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 131755336656857) ^ 152671305512 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 131755336656857) ^ 75944 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_146721485958499 : Nat.Prime 146721485958499 := by
  apply lucas_primality 146721485958499 (2 : ZMod 146721485958499)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (11, 1), (421, 1), (65190253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (11, 1), (421, 1), (65190253, 1)] : List FactorBlock).map factorBlockValue).prod) = 146721485958499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_421
      · exact prime_eightyFourCD_65190253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 146721485958499) ^ 73360742979249 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 146721485958499) ^ 48907161986166 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 146721485958499) ^ 13338316905318 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 146721485958499) ^ 348507092538 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 146721485958499) ^ 2250666 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_181378014454621 : Nat.Prime 181378014454621 := by
  apply lucas_primality 181378014454621 (6 : ZMod 181378014454621)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (335885211953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (335885211953, 1)] : List FactorBlock).map factorBlockValue).prod) = 181378014454621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_335885211953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 181378014454621) ^ 90689007227310 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 181378014454621) ^ 60459338151540 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 181378014454621) ^ 36275602890924 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 181378014454621) ^ 540 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_181938416650483 : Nat.Prime 181938416650483 := by
  apply lucas_primality 181938416650483 (3 : ZMod 181938416650483)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9413, 1), (27817, 1), (115807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9413, 1), (27817, 1), (115807, 1)] : List FactorBlock).map factorBlockValue).prod) = 181938416650483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_9413
      · exact prime_eightyFourCD_27817
      · exact prime_eightyFourCD_115807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 181938416650483) ^ 90969208325241 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 181938416650483) ^ 60646138883494 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 181938416650483) ^ 19328419914 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 181938416650483) ^ 6540547746 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 181938416650483) ^ 1571048526 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_196700577683231 : Nat.Prime 196700577683231 := by
  apply lucas_primality 196700577683231 (13 : ZMod 196700577683231)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (383, 1), (51357853181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (383, 1), (51357853181, 1)] : List FactorBlock).map factorBlockValue).prod) = 196700577683231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_383
      · exact prime_eightyFourCD_51357853181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 196700577683231) ^ 98350288841615 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 196700577683231) ^ 39340115536646 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 196700577683231) ^ 513578531810 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 196700577683231) ^ 3830 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_342139957225553 : Nat.Prime 342139957225553 := by
  apply lucas_primality 342139957225553 (3 : ZMod 342139957225553)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (83, 1), (257635509959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (83, 1), (257635509959, 1)] : List FactorBlock).map factorBlockValue).prod) = 342139957225553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_83
      · exact prime_eightyFourCD_257635509959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 342139957225553) ^ 171069978612776 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 342139957225553) ^ 4122168159344 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 342139957225553) ^ 1328 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_391594514796007 : Nat.Prime 391594514796007 := by
  apply lucas_primality 391594514796007 (19 : ZMod 391594514796007)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (223621, 1), (4946759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (223621, 1), (4946759, 1)] : List FactorBlock).map factorBlockValue).prod) = 391594514796007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_59
      · exact prime_eightyFourCD_223621
      · exact prime_eightyFourCD_4946759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 391594514796007) ^ 195797257398003 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (19 : ZMod 391594514796007) ^ 130531504932002 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (19 : ZMod 391594514796007) ^ 6637195166034 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (19 : ZMod 391594514796007) ^ 1751152686 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (19 : ZMod 391594514796007) ^ 79161834 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_412335268310003 : Nat.Prime 412335268310003 := by
  apply lucas_primality 412335268310003 (2 : ZMod 412335268310003)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (977, 1), (211021119913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (977, 1), (211021119913, 1)] : List FactorBlock).map factorBlockValue).prod) = 412335268310003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_977
      · exact prime_eightyFourCD_211021119913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 412335268310003) ^ 206167634155001 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 412335268310003) ^ 422042239826 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 412335268310003) ^ 1954 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_629430587940277 : Nat.Prime 629430587940277 := by
  apply lucas_primality 629430587940277 (2 : ZMod 629430587940277)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5828060999447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5828060999447, 1)] : List FactorBlock).map factorBlockValue).prod) = 629430587940277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5828060999447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 629430587940277) ^ 314715293970138 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 629430587940277) ^ 209810195980092 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 629430587940277) ^ 108 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_646103848179679 : Nat.Prime 646103848179679 := by
  apply lucas_primality 646103848179679 (7 : ZMod 646103848179679)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23, 1), (283, 1), (5807, 1), (406993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23, 1), (283, 1), (5807, 1), (406993, 1)] : List FactorBlock).map factorBlockValue).prod) = 646103848179679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_23
      · exact prime_eightyFourCD_283
      · exact prime_eightyFourCD_5807
      · exact prime_eightyFourCD_406993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 646103848179679) ^ 323051924089839 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 646103848179679) ^ 215367949393226 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 646103848179679) ^ 92300549739954 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 646103848179679) ^ 28091471659986 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 646103848179679) ^ 2283052467066 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 646103848179679) ^ 111262932354 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 646103848179679) ^ 1587506046 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_707734513137907 : Nat.Prime 707734513137907 := by
  apply lucas_primality 707734513137907 (2 : ZMod 707734513137907)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (37, 1), (101, 1), (3507143347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (37, 1), (101, 1), (3507143347, 1)] : List FactorBlock).map factorBlockValue).prod) = 707734513137907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_37
      · exact prime_eightyFourCD_101
      · exact prime_eightyFourCD_3507143347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 707734513137907) ^ 353867256568953 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 707734513137907) ^ 235911504379302 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 707734513137907) ^ 19127959814538 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 707734513137907) ^ 7007272407306 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 707734513137907) ^ 201798 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_972844523126627 : Nat.Prime 972844523126627 := by
  apply lucas_primality 972844523126627 (2 : ZMod 972844523126627)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 2), (1217, 1), (19079, 1), (58031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 2), (1217, 1), (19079, 1), (58031, 1)] : List FactorBlock).map factorBlockValue).prod) = 972844523126627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_19
      · exact prime_eightyFourCD_1217
      · exact prime_eightyFourCD_19079
      · exact prime_eightyFourCD_58031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 972844523126627) ^ 486422261563313 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 972844523126627) ^ 51202343322454 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 972844523126627) ^ 799379230178 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 972844523126627) ^ 50990330894 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 972844523126627) ^ 16764221246 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1302393682573453 : Nat.Prime 1302393682573453 := by
  apply lucas_primality 1302393682573453 (2 : ZMod 1302393682573453)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (17, 1), (151, 1), (671111401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (17, 1), (151, 1), (671111401, 1)] : List FactorBlock).map factorBlockValue).prod) = 1302393682573453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_17
      · exact prime_eightyFourCD_151
      · exact prime_eightyFourCD_671111401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1302393682573453) ^ 651196841286726 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1302393682573453) ^ 434131227524484 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1302393682573453) ^ 186056240367636 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1302393682573453) ^ 76611393092556 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1302393682573453) ^ 8625123725652 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1302393682573453) ^ 1940652 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1549234023645131 : Nat.Prime 1549234023645131 := by
  apply lucas_primality 1549234023645131 (6 : ZMod 1549234023645131)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (6547, 1), (11821, 1), (2001799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (6547, 1), (11821, 1), (2001799, 1)] : List FactorBlock).map factorBlockValue).prod) = 1549234023645131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_6547
      · exact prime_eightyFourCD_11821
      · exact prime_eightyFourCD_2001799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1549234023645131) ^ 774617011822565 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1549234023645131) ^ 309846804729026 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1549234023645131) ^ 236632659790 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1549234023645131) ^ 131057780530 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1549234023645131) ^ 773920870 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1759129065237073 : Nat.Prime 1759129065237073 := by
  apply lucas_primality 1759129065237073 (5 : ZMod 1759129065237073)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (193, 1), (1373, 1), (138302051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (193, 1), (1373, 1), (138302051, 1)] : List FactorBlock).map factorBlockValue).prod) = 1759129065237073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_193
      · exact prime_eightyFourCD_1373
      · exact prime_eightyFourCD_138302051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1759129065237073) ^ 879564532618536 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1759129065237073) ^ 586376355079024 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1759129065237073) ^ 9114658369104 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1759129065237073) ^ 1281230200464 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1759129065237073) ^ 12719472 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_2194853618936911 : Nat.Prime 2194853618936911 := by
  apply lucas_primality 2194853618936911 (17 : ZMod 2194853618936911)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31319, 1), (2336019263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31319, 1), (2336019263, 1)] : List FactorBlock).map factorBlockValue).prod) = 2194853618936911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_31319
      · exact prime_eightyFourCD_2336019263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 2194853618936911) ^ 1097426809468455 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (17 : ZMod 2194853618936911) ^ 731617872978970 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (17 : ZMod 2194853618936911) ^ 438970723787382 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (17 : ZMod 2194853618936911) ^ 70080577890 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (17 : ZMod 2194853618936911) ^ 939570 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_2378408968073533 : Nat.Prime 2378408968073533 := by
  apply lucas_primality 2378408968073533 (2 : ZMod 2378408968073533)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (251, 1), (789644411711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (251, 1), (789644411711, 1)] : List FactorBlock).map factorBlockValue).prod) = 2378408968073533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_251
      · exact prime_eightyFourCD_789644411711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2378408968073533) ^ 1189204484036766 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2378408968073533) ^ 792802989357844 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2378408968073533) ^ 9475732940532 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2378408968073533) ^ 3012 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_3098468047290263 : Nat.Prime 3098468047290263 := by
  apply lucas_primality 3098468047290263 (5 : ZMod 3098468047290263)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1549234023645131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1549234023645131, 1)] : List FactorBlock).map factorBlockValue).prod) = 3098468047290263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_1549234023645131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 3098468047290263) ^ 1549234023645131 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3098468047290263) ^ 2 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_4151246808484493 : Nat.Prime 4151246808484493 := by
  apply lucas_primality 4151246808484493 (3 : ZMod 4151246808484493)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (5433569121053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (5433569121053, 1)] : List FactorBlock).map factorBlockValue).prod) = 4151246808484493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_191
      · exact prime_eightyFourCD_5433569121053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4151246808484493) ^ 2075623404242246 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4151246808484493) ^ 21734276484212 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4151246808484493) ^ 764 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_5159426319336379 : Nat.Prime 5159426319336379 := by
  apply lucas_primality 5159426319336379 (2 : ZMod 5159426319336379)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (255887, 1), (3360484849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (255887, 1), (3360484849, 1)] : List FactorBlock).map factorBlockValue).prod) = 5159426319336379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_255887
      · exact prime_eightyFourCD_3360484849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5159426319336379) ^ 2579713159668189 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5159426319336379) ^ 1719808773112126 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5159426319336379) ^ 20162909094 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5159426319336379) ^ 1535322 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_5721379479820937 : Nat.Prime 5721379479820937 := by
  apply lucas_primality 5721379479820937 (3 : ZMod 5721379479820937)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (503, 1), (61817999393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (503, 1), (61817999393, 1)] : List FactorBlock).map factorBlockValue).prod) = 5721379479820937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_23
      · exact prime_eightyFourCD_503
      · exact prime_eightyFourCD_61817999393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5721379479820937) ^ 2860689739910468 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5721379479820937) ^ 248755629557432 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5721379479820937) ^ 11374511888312 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5721379479820937) ^ 92552 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_6472255209000863 : Nat.Prime 6472255209000863 := by
  apply lucas_primality 6472255209000863 (5 : ZMod 6472255209000863)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (31, 1), (20359, 1), (176811091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (31, 1), (20359, 1), (176811091, 1)] : List FactorBlock).map factorBlockValue).prod) = 6472255209000863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_29
      · exact prime_eightyFourCD_31
      · exact prime_eightyFourCD_20359
      · exact prime_eightyFourCD_176811091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6472255209000863) ^ 3236127604500431 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 6472255209000863) ^ 223181214103478 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 6472255209000863) ^ 208782426096802 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 6472255209000863) ^ 317906341618 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 6472255209000863) ^ 36605482 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_9502853395587581 : Nat.Prime 9502853395587581 := by
  apply lucas_primality 9502853395587581 (2 : ZMod 9502853395587581)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (31, 1), (43, 1), (59, 1), (123295093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (31, 1), (43, 1), (59, 1), (123295093, 1)] : List FactorBlock).map factorBlockValue).prod) = 9502853395587581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_31
      · exact prime_eightyFourCD_43
      · exact prime_eightyFourCD_59
      · exact prime_eightyFourCD_123295093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9502853395587581) ^ 4751426697793790 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9502853395587581) ^ 1900570679117516 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9502853395587581) ^ 1357550485083940 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9502853395587581) ^ 306543657922180 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9502853395587581) ^ 220996590595060 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9502853395587581) ^ 161065311789620 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9502853395587581) ^ 77074060 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_11653019889088321 : Nat.Prime 11653019889088321 := by
  apply lucas_primality 11653019889088321 (11 : ZMod 11653019889088321)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 1), (193, 1), (8353, 1), (2509841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 1), (193, 1), (8353, 1), (2509841, 1)] : List FactorBlock).map factorBlockValue).prod) = 11653019889088321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_193
      · exact prime_eightyFourCD_8353
      · exact prime_eightyFourCD_2509841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 11653019889088321) ^ 5826509944544160 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 11653019889088321) ^ 3884339963029440 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 11653019889088321) ^ 2330603977817664 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 11653019889088321) ^ 60378341394240 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 11653019889088321) ^ 1395070021440 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 11653019889088321) ^ 4642931520 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_13200142826062729 : Nat.Prime 13200142826062729 := by
  apply lucas_primality 13200142826062729 (14 : ZMod 13200142826062729)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (487, 1), (937, 1), (14880373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (487, 1), (937, 1), (14880373, 1)] : List FactorBlock).map factorBlockValue).prod) = 13200142826062729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_487
      · exact prime_eightyFourCD_937
      · exact prime_eightyFourCD_14880373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 13200142826062729) ^ 6600071413031364 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (14 : ZMod 13200142826062729) ^ 4400047608687576 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (14 : ZMod 13200142826062729) ^ 27105016069944 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (14 : ZMod 13200142826062729) ^ 14087665769544 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (14 : ZMod 13200142826062729) ^ 887084136 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_34392043143319369 : Nat.Prime 34392043143319369 := by
  apply lucas_primality 34392043143319369 (11 : ZMod 34392043143319369)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (110230907510639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (110230907510639, 1)] : List FactorBlock).map factorBlockValue).prod) = 34392043143319369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_110230907510639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 34392043143319369) ^ 17196021571659684 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 34392043143319369) ^ 11464014381106456 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 34392043143319369) ^ 2645541780255336 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 34392043143319369) ^ 312 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_37059712430045443 : Nat.Prime 37059712430045443 := by
  apply lucas_primality 37059712430045443 (2 : ZMod 37059712430045443)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (163, 1), (1093, 1), (34669136773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (163, 1), (1093, 1), (34669136773, 1)] : List FactorBlock).map factorBlockValue).prod) = 37059712430045443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_163
      · exact prime_eightyFourCD_1093
      · exact prime_eightyFourCD_34669136773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37059712430045443) ^ 18529856215022721 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 37059712430045443) ^ 12353237476681814 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 37059712430045443) ^ 227360198957334 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 37059712430045443) ^ 33906415763994 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 37059712430045443) ^ 1068954 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_50697765176933141 : Nat.Prime 50697765176933141 := by
  apply lucas_primality 50697765176933141 (2 : ZMod 50697765176933141)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (239, 1), (523, 1), (2897084683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (239, 1), (523, 1), (2897084683, 1)] : List FactorBlock).map factorBlockValue).prod) = 50697765176933141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_239
      · exact prime_eightyFourCD_523
      · exact prime_eightyFourCD_2897084683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50697765176933141) ^ 25348882588466570 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 50697765176933141) ^ 10139553035386628 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 50697765176933141) ^ 7242537882419020 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 50697765176933141) ^ 212124540489260 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 50697765176933141) ^ 96936453493180 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 50697765176933141) ^ 17499580 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_61835038188991919 : Nat.Prime 61835038188991919 := by
  apply lucas_primality 61835038188991919 (11 : ZMod 61835038188991919)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (239, 1), (129362004579481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (239, 1), (129362004579481, 1)] : List FactorBlock).map factorBlockValue).prod) = 61835038188991919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_239
      · exact prime_eightyFourCD_129362004579481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 61835038188991919) ^ 30917519094495959 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 61835038188991919) ^ 258724009158962 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 61835038188991919) ^ 478 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_88500360343897583 : Nat.Prime 88500360343897583 := by
  apply lucas_primality 88500360343897583 (5 : ZMod 88500360343897583)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (391594514796007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (391594514796007, 1)] : List FactorBlock).map factorBlockValue).prod) = 88500360343897583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_113
      · exact prime_eightyFourCD_391594514796007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 88500360343897583) ^ 44250180171948791 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 88500360343897583) ^ 783189029592014 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 88500360343897583) ^ 226 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_163977980099527507 : Nat.Prime 163977980099527507 := by
  apply lucas_primality 163977980099527507 (2 : ZMod 163977980099527507)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (67, 1), (37082311193923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (67, 1), (37082311193923, 1)] : List FactorBlock).map factorBlockValue).prod) = 163977980099527507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_67
      · exact prime_eightyFourCD_37082311193923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 163977980099527507) ^ 81988990049763753 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 163977980099527507) ^ 54659326699842502 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 163977980099527507) ^ 14907089099957046 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 163977980099527507) ^ 2447432538798918 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 163977980099527507) ^ 4422 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_249456777624600859 : Nat.Prime 249456777624600859 := by
  apply lucas_primality 249456777624600859 (2 : ZMod 249456777624600859)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (13, 1), (1567, 1), (8443, 1), (2984351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (13, 1), (1567, 1), (8443, 1), (2984351, 1)] : List FactorBlock).map factorBlockValue).prod) = 249456777624600859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_1567
      · exact prime_eightyFourCD_8443
      · exact prime_eightyFourCD_2984351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 249456777624600859) ^ 124728388812300429 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 249456777624600859) ^ 83152259208200286 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 249456777624600859) ^ 19188982894200066 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 249456777624600859) ^ 159193859364774 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 249456777624600859) ^ 29545988111406 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 249456777624600859) ^ 83588283558 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_314105458523230111 : Nat.Prime 314105458523230111 := by
  apply lucas_primality 314105458523230111 (6 : ZMod 314105458523230111)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (29, 1), (7589, 1), (4324929107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (29, 1), (7589, 1), (4324929107, 1)] : List FactorBlock).map factorBlockValue).prod) = 314105458523230111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_29
      · exact prime_eightyFourCD_7589
      · exact prime_eightyFourCD_4324929107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 314105458523230111) ^ 157052729261615055 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 314105458523230111) ^ 104701819507743370 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 314105458523230111) ^ 62821091704646022 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 314105458523230111) ^ 28555041683930010 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 314105458523230111) ^ 10831222707697590 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 314105458523230111) ^ 41389571553990 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 314105458523230111) ^ 72626730 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_482266027735322221 : Nat.Prime 482266027735322221 := by
  apply lucas_primality 482266027735322221 (10 : ZMod 482266027735322221)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (13, 1), (17, 1), (19, 1), (160409, 1), (1325923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (13, 1), (17, 1), (19, 1), (160409, 1), (1325923, 1)] : List FactorBlock).map factorBlockValue).prod) = 482266027735322221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_17
      · exact prime_eightyFourCD_19
      · exact prime_eightyFourCD_160409
      · exact prime_eightyFourCD_1325923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 482266027735322221) ^ 241133013867661110 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 482266027735322221) ^ 160755342578440740 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 482266027735322221) ^ 96453205547064444 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 482266027735322221) ^ 37097386748870940 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 482266027735322221) ^ 28368589866783660 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 482266027735322221) ^ 25382422512385380 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 482266027735322221) ^ 3006477365580 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 482266027735322221) ^ 363720991140 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_531752808356481553 : Nat.Prime 531752808356481553 := by
  apply lucas_primality 531752808356481553 (10 : ZMod 531752808356481553)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 2), (294551, 1), (71097181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 2), (294551, 1), (71097181, 1)] : List FactorBlock).map factorBlockValue).prod) = 531752808356481553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_23
      · exact prime_eightyFourCD_294551
      · exact prime_eightyFourCD_71097181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 531752808356481553) ^ 265876404178240776 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 531752808356481553) ^ 177250936118827184 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 531752808356481553) ^ 23119687319847024 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 531752808356481553) ^ 1805299619952 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 531752808356481553) ^ 7479238992 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_597576355001655779 : Nat.Prime 597576355001655779 := by
  apply lucas_primality 597576355001655779 (2 : ZMod 597576355001655779)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (31, 1), (196700577683231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (31, 1), (196700577683231, 1)] : List FactorBlock).map factorBlockValue).prod) = 597576355001655779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_31
      · exact prime_eightyFourCD_196700577683231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 597576355001655779) ^ 298788177500827889 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 597576355001655779) ^ 85368050714522254 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 597576355001655779) ^ 19276656612956638 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 597576355001655779) ^ 3038 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1287188348581953703 : Nat.Prime 1287188348581953703 := by
  apply lucas_primality 1287188348581953703 (5 : ZMod 1287188348581953703)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3533, 1), (3761, 1), (5381738903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3533, 1), (3761, 1), (5381738903, 1)] : List FactorBlock).map factorBlockValue).prod) = 1287188348581953703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_3533
      · exact prime_eightyFourCD_3761
      · exact prime_eightyFourCD_5381738903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1287188348581953703) ^ 643594174290976851 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1287188348581953703) ^ 429062782860651234 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1287188348581953703) ^ 364332960255294 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1287188348581953703) ^ 342246303797382 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1287188348581953703) ^ 239177034 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1688234165419289101 : Nat.Prime 1688234165419289101 := by
  apply lucas_primality 1688234165419289101 (2 : ZMod 1688234165419289101)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (43, 1), (2903, 1), (45081248893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (43, 1), (2903, 1), (45081248893, 1)] : List FactorBlock).map factorBlockValue).prod) = 1688234165419289101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_43
      · exact prime_eightyFourCD_2903
      · exact prime_eightyFourCD_45081248893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1688234165419289101) ^ 844117082709644550 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1688234165419289101) ^ 562744721806429700 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1688234165419289101) ^ 337646833083857820 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1688234165419289101) ^ 39261259660913700 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1688234165419289101) ^ 581548110719700 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1688234165419289101) ^ 37448700 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_2981700566578430251 : Nat.Prime 2981700566578430251 := by
  apply lucas_primality 2981700566578430251 (2 : ZMod 2981700566578430251)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (101, 1), (39362383717207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (101, 1), (39362383717207, 1)] : List FactorBlock).map factorBlockValue).prod) = 2981700566578430251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_101
      · exact prime_eightyFourCD_39362383717207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2981700566578430251) ^ 1490850283289215125 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2981700566578430251) ^ 993900188859476750 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2981700566578430251) ^ 596340113315686050 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2981700566578430251) ^ 29521787787905250 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2981700566578430251) ^ 75750 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_2994173031470456471 : Nat.Prime 2994173031470456471 := by
  apply lucas_primality 2994173031470456471 (11 : ZMod 2994173031470456471)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (167, 1), (43729706900401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (167, 1), (43729706900401, 1)] : List FactorBlock).map factorBlockValue).prod) = 2994173031470456471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_41
      · exact prime_eightyFourCD_167
      · exact prime_eightyFourCD_43729706900401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2994173031470456471) ^ 1497086515735228235 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 2994173031470456471) ^ 598834606294091294 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 2994173031470456471) ^ 73028610523669670 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 2994173031470456471) ^ 17929179829164410 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 2994173031470456471) ^ 68470 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_4863406943289134531 : Nat.Prime 4863406943289134531 := by
  apply lucas_primality 4863406943289134531 (6 : ZMod 4863406943289134531)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (107, 1), (647, 1), (2251, 1), (183581171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (107, 1), (647, 1), (2251, 1), (183581171, 1)] : List FactorBlock).map factorBlockValue).prod) = 4863406943289134531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_17
      · exact prime_eightyFourCD_107
      · exact prime_eightyFourCD_647
      · exact prime_eightyFourCD_2251
      · exact prime_eightyFourCD_183581171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4863406943289134531) ^ 2431703471644567265 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 4863406943289134531) ^ 972681388657826906 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 4863406943289134531) ^ 286082761369949090 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 4863406943289134531) ^ 45452401339150790 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 4863406943289134531) ^ 7516857717602990 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 4863406943289134531) ^ 2160553950817030 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 4863406943289134531) ^ 26491861430 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_4943538588207987697 : Nat.Prime 4943538588207987697 := by
  apply lucas_primality 4943538588207987697 (5 : ZMod 4943538588207987697)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (12889, 1), (203591, 1), (39248123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (12889, 1), (203591, 1), (39248123, 1)] : List FactorBlock).map factorBlockValue).prod) = 4943538588207987697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_12889
      · exact prime_eightyFourCD_203591
      · exact prime_eightyFourCD_39248123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4943538588207987697) ^ 2471769294103993848 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 4943538588207987697) ^ 1647846196069329232 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 4943538588207987697) ^ 383547101265264 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 4943538588207987697) ^ 24281714752656 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 4943538588207987697) ^ 125956051152 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_7483703328738025771 : Nat.Prime 7483703328738025771 := by
  apply lucas_primality 7483703328738025771 (2 : ZMod 7483703328738025771)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (249456777624600859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (249456777624600859, 1)] : List FactorBlock).map factorBlockValue).prod) = 7483703328738025771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_249456777624600859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7483703328738025771) ^ 3741851664369012885 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7483703328738025771) ^ 2494567776246008590 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7483703328738025771) ^ 1496740665747605154 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7483703328738025771) ^ 30 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_7582948862008351687 : Nat.Prime 7582948862008351687 := by
  apply lucas_primality 7582948862008351687 (5 : ZMod 7582948862008351687)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (101, 1), (103, 1), (1991583150407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (101, 1), (103, 1), (1991583150407, 1)] : List FactorBlock).map factorBlockValue).prod) = 7582948862008351687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_61
      · exact prime_eightyFourCD_101
      · exact prime_eightyFourCD_103
      · exact prime_eightyFourCD_1991583150407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7582948862008351687) ^ 3791474431004175843 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 7582948862008351687) ^ 2527649620669450562 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 7582948862008351687) ^ 124310637082104126 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 7582948862008351687) ^ 75078701604043086 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 7582948862008351687) ^ 73620862737945162 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 7582948862008351687) ^ 3807498 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_7852932686361389021 : Nat.Prime 7852932686361389021 := by
  apply lucas_primality 7852932686361389021 (2 : ZMod 7852932686361389021)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (503, 1), (4801, 1), (162593128717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (503, 1), (4801, 1), (162593128717, 1)] : List FactorBlock).map factorBlockValue).prod) = 7852932686361389021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_503
      · exact prime_eightyFourCD_4801
      · exact prime_eightyFourCD_162593128717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7852932686361389021) ^ 3926466343180694510 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7852932686361389021) ^ 1570586537272277804 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7852932686361389021) ^ 15612192219406340 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7852932686361389021) ^ 1635686874893020 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7852932686361389021) ^ 48298060 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_8451140311072988803 : Nat.Prime 8451140311072988803 := by
  apply lucas_primality 8451140311072988803 (7 : ZMod 8451140311072988803)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 1), (5159426319336379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 1), (5159426319336379, 1)] : List FactorBlock).map factorBlockValue).prod) = 8451140311072988803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_5159426319336379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8451140311072988803) ^ 4225570155536494401 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 8451140311072988803) ^ 2817046770357662934 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 8451140311072988803) ^ 1207305758724712686 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 8451140311072988803) ^ 650087716236383754 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 8451140311072988803) ^ 1638 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_8690764705513186619 : Nat.Prime 8690764705513186619 := by
  apply lucas_primality 8690764705513186619 (2 : ZMod 8690764705513186619)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (5102731, 1), (121654248977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (5102731, 1), (121654248977, 1)] : List FactorBlock).map factorBlockValue).prod) = 8690764705513186619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_5102731
      · exact prime_eightyFourCD_121654248977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8690764705513186619) ^ 4345382352756593309 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8690764705513186619) ^ 1241537815073312374 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8690764705513186619) ^ 1703159485678 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8690764705513186619) ^ 71438234 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_9137624547850147991 : Nat.Prime 9137624547850147991 := by
  apply lucas_primality 9137624547850147991 (11 : ZMod 9137624547850147991)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (103, 1), (6311623, 1), (1405578271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (103, 1), (6311623, 1), (1405578271, 1)] : List FactorBlock).map factorBlockValue).prod) = 9137624547850147991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_103
      · exact prime_eightyFourCD_6311623
      · exact prime_eightyFourCD_1405578271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 9137624547850147991) ^ 4568812273925073995 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 9137624547850147991) ^ 1827524909570029598 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 9137624547850147991) ^ 88714801435438330 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 9137624547850147991) ^ 1447745619130 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (11 : ZMod 9137624547850147991) ^ 6500971690 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_10449268633520056001 : Nat.Prime 10449268633520056001 := by
  apply lucas_primality 10449268633520056001 (3 : ZMod 10449268633520056001)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 3), (2963, 1), (440823010189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 3), (2963, 1), (440823010189, 1)] : List FactorBlock).map factorBlockValue).prod) = 10449268633520056001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_2963
      · exact prime_eightyFourCD_440823010189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10449268633520056001) ^ 5224634316760028000 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 10449268633520056001) ^ 2089853726704011200 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 10449268633520056001) ^ 3526584081512000 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 10449268633520056001) ^ 23704000 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_27896840881203395081 : Nat.Prime 27896840881203395081 := by
  apply lucas_primality 27896840881203395081 (6 : ZMod 27896840881203395081)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (19, 1), (53, 1), (83, 1), (495133, 1), (2407507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (19, 1), (53, 1), (83, 1), (495133, 1), (2407507, 1)] : List FactorBlock).map factorBlockValue).prod) = 27896840881203395081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_19
      · exact prime_eightyFourCD_53
      · exact prime_eightyFourCD_83
      · exact prime_eightyFourCD_495133
      · exact prime_eightyFourCD_2407507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 27896840881203395081) ^ 13948420440601697540 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 27896840881203395081) ^ 5579368176240679016 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 27896840881203395081) ^ 3985262983029056440 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 27896840881203395081) ^ 1468254783221231320 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 27896840881203395081) ^ 526355488324592360 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 27896840881203395081) ^ 336106516641004760 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 27896840881203395081) ^ 56342115918760 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 27896840881203395081) ^ 11587439156440 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_30427265284783672423 : Nat.Prime 30427265284783672423 := by
  apply lucas_primality 30427265284783672423 (3 : ZMod 30427265284783672423)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19, 1), (3733111, 1), (5499760961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19, 1), (3733111, 1), (5499760961, 1)] : List FactorBlock).map factorBlockValue).prod) = 30427265284783672423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_19
      · exact prime_eightyFourCD_3733111
      · exact prime_eightyFourCD_5499760961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30427265284783672423) ^ 15213632642391836211 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 30427265284783672423) ^ 10142421761594557474 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 30427265284783672423) ^ 2340558868060282494 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 30427265284783672423) ^ 1601435014988614338 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 30427265284783672423) ^ 8150645744202 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 30427265284783672423) ^ 5532470502 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_81957748154205629131 : Nat.Prime 81957748154205629131 := by
  apply lucas_primality 81957748154205629131 (3 : ZMod 81957748154205629131)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (15218597, 1), (179512272943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (15218597, 1), (179512272943, 1)] : List FactorBlock).map factorBlockValue).prod) = 81957748154205629131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_15218597
      · exact prime_eightyFourCD_179512272943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 81957748154205629131) ^ 40978874077102814565 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 81957748154205629131) ^ 27319249384735209710 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 81957748154205629131) ^ 16391549630841125826 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 81957748154205629131) ^ 5385368188290 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 81957748154205629131) ^ 456557910 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_153732948943606501171 : Nat.Prime 153732948943606501171 := by
  apply lucas_primality 153732948943606501171 (2 : ZMod 153732948943606501171)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (31, 1), (211, 1), (60264034333183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (31, 1), (211, 1), (60264034333183, 1)] : List FactorBlock).map factorBlockValue).prod) = 153732948943606501171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_13
      · exact prime_eightyFourCD_31
      · exact prime_eightyFourCD_211
      · exact prime_eightyFourCD_60264034333183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 153732948943606501171) ^ 76866474471803250585 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 153732948943606501171) ^ 51244316314535500390 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 153732948943606501171) ^ 30746589788721300234 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 153732948943606501171) ^ 11825611457200500090 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 153732948943606501171) ^ 4959127385277629070 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 153732948943606501171) ^ 728592175088182470 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 153732948943606501171) ^ 2550990 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_173294439271736807159 : Nat.Prime 173294439271736807159 := by
  apply lucas_primality 173294439271736807159 (7 : ZMod 173294439271736807159)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (47, 1), (12211, 1), (15683, 1), (33310301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (47, 1), (12211, 1), (15683, 1), (33310301, 1)] : List FactorBlock).map factorBlockValue).prod) = 173294439271736807159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_17
      · exact prime_eightyFourCD_47
      · exact prime_eightyFourCD_12211
      · exact prime_eightyFourCD_15683
      · exact prime_eightyFourCD_33310301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 173294439271736807159) ^ 86647219635868403579 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 173294439271736807159) ^ 10193790545396282774 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 173294439271736807159) ^ 3687115729185889514 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 173294439271736807159) ^ 14191666470537778 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 173294439271736807159) ^ 11049827154991826 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 173294439271736807159) ^ 5202427899758 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_272986159032300660733 : Nat.Prime 272986159032300660733 := by
  apply lucas_primality 272986159032300660733 (2 : ZMod 272986159032300660733)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7582948862008351687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7582948862008351687, 1)] : List FactorBlock).map factorBlockValue).prod) = 272986159032300660733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_7582948862008351687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 272986159032300660733) ^ 136493079516150330366 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 272986159032300660733) ^ 90995386344100220244 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 272986159032300660733) ^ 36 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_284316895490379362201 : Nat.Prime 284316895490379362201 := by
  apply lucas_primality 284316895490379362201 (3 : ZMod 284316895490379362201)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (9689, 1), (146721485958499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (9689, 1), (146721485958499, 1)] : List FactorBlock).map factorBlockValue).prod) = 284316895490379362201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_9689
      · exact prime_eightyFourCD_146721485958499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 284316895490379362201) ^ 142158447745189681100 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 284316895490379362201) ^ 56863379098075872440 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 284316895490379362201) ^ 29344297191699800 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 284316895490379362201) ^ 1937800 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_2002420280269044629789 : Nat.Prime 2002420280269044629789 := by
  apply lucas_primality 2002420280269044629789 (2 : ZMod 2002420280269044629789)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (461, 1), (7757, 1), (56453, 1), (2479781987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (461, 1), (7757, 1), (56453, 1), (2479781987, 1)] : List FactorBlock).map factorBlockValue).prod) = 2002420280269044629789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_461
      · exact prime_eightyFourCD_7757
      · exact prime_eightyFourCD_56453
      · exact prime_eightyFourCD_2479781987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2002420280269044629789) ^ 1001210140134522314894 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2002420280269044629789) ^ 4343644859585780108 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2002420280269044629789) ^ 258143648352332684 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2002420280269044629789) ^ 35470573402105196 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2002420280269044629789) ^ 807498518324 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_2426122149804315300227 : Nat.Prime 2426122149804315300227 := by
  apply lucas_primality 2426122149804315300227 (2 : ZMod 2426122149804315300227)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (173294439271736807159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (173294439271736807159, 1)] : List FactorBlock).map factorBlockValue).prod) = 2426122149804315300227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_173294439271736807159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2426122149804315300227) ^ 1213061074902157650113 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2426122149804315300227) ^ 346588878543473614318 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2426122149804315300227) ^ 14 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_5201192402228866274767 : Nat.Prime 5201192402228866274767 := by
  apply lucas_primality 5201192402228866274767 (3 : ZMod 5201192402228866274767)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4673, 1), (61835038188991919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4673, 1), (61835038188991919, 1)] : List FactorBlock).map factorBlockValue).prod) = 5201192402228866274767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_4673
      · exact prime_eightyFourCD_61835038188991919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5201192402228866274767) ^ 2600596201114433137383 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5201192402228866274767) ^ 1733730800742955424922 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5201192402228866274767) ^ 1113030687401854542 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5201192402228866274767) ^ 84114 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_11200110688412798417911 : Nat.Prime 11200110688412798417911 := by
  apply lucas_primality 11200110688412798417911 (3 : ZMod 11200110688412798417911)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (43, 1), (269, 1), (520393, 1), (20674148129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (43, 1), (269, 1), (520393, 1), (20674148129, 1)] : List FactorBlock).map factorBlockValue).prod) = 11200110688412798417911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_43
      · exact prime_eightyFourCD_269
      · exact prime_eightyFourCD_520393
      · exact prime_eightyFourCD_20674148129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11200110688412798417911) ^ 5600055344206399208955 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 11200110688412798417911) ^ 3733370229470932805970 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 11200110688412798417911) ^ 2240022137682559683582 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 11200110688412798417911) ^ 260467690428204614370 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 11200110688412798417911) ^ 41636099213430477390 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 11200110688412798417911) ^ 21522408426732870 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 11200110688412798417911) ^ 541744724790 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_21530854024988147363767 : Nat.Prime 21530854024988147363767 := by
  apply lucas_primality 21530854024988147363767 (5 : ZMod 21530854024988147363767)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (111331093, 1), (2930224182607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (111331093, 1), (2930224182607, 1)] : List FactorBlock).map factorBlockValue).prod) = 21530854024988147363767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_111331093
      · exact prime_eightyFourCD_2930224182607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21530854024988147363767) ^ 10765427012494073681883 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 21530854024988147363767) ^ 7176951341662715787922 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 21530854024988147363767) ^ 1957350365908013396706 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 21530854024988147363767) ^ 193394796052062 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 21530854024988147363767) ^ 7347852138 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_22717053951720706097083 : Nat.Prime 22717053951720706097083 := by
  apply lucas_primality 22717053951720706097083 (2 : ZMod 22717053951720706097083)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (17, 1), (61, 1), (139, 1), (972844523126627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (17, 1), (61, 1), (139, 1), (972844523126627, 1)] : List FactorBlock).map factorBlockValue).prod) = 22717053951720706097083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_17
      · exact prime_eightyFourCD_61
      · exact prime_eightyFourCD_139
      · exact prime_eightyFourCD_972844523126627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22717053951720706097083) ^ 11358526975860353048541 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 22717053951720706097083) ^ 7572351317240235365694 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 22717053951720706097083) ^ 1336297291277688593946 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 22717053951720706097083) ^ 372410720520011575362 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 22717053951720706097083) ^ 163432042818134576238 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 22717053951720706097083) ^ 23351166 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_25513123047606161882911 : Nat.Prime 25513123047606161882911 := by
  apply lucas_primality 25513123047606161882911 (3 : ZMod 25513123047606161882911)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (23, 1), (22651, 1), (181378014454621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (23, 1), (22651, 1), (181378014454621, 1)] : List FactorBlock).map factorBlockValue).prod) = 25513123047606161882911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_23
      · exact prime_eightyFourCD_22651
      · exact prime_eightyFourCD_181378014454621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 25513123047606161882911) ^ 12756561523803080941455 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 25513123047606161882911) ^ 8504374349202053960970 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 25513123047606161882911) ^ 5102624609521232376582 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 25513123047606161882911) ^ 1109266219461137473170 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 25513123047606161882911) ^ 1126357469763196410 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 25513123047606161882911) ^ 140662710 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_34298098387100667679369 : Nat.Prime 34298098387100667679369 := by
  apply lucas_primality 34298098387100667679369 (7 : ZMod 34298098387100667679369)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (409, 1), (11824817, 1), (295488826819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (409, 1), (11824817, 1), (295488826819, 1)] : List FactorBlock).map factorBlockValue).prod) = 34298098387100667679369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_409
      · exact prime_eightyFourCD_11824817
      · exact prime_eightyFourCD_295488826819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 34298098387100667679369) ^ 17149049193550333839684 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 34298098387100667679369) ^ 11432699462366889226456 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 34298098387100667679369) ^ 83858431264304810952 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 34298098387100667679369) ^ 2900518324055304 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 34298098387100667679369) ^ 116072403672 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_39206980188788485360297 : Nat.Prime 39206980188788485360297 := by
  apply lucas_primality 39206980188788485360297 (7 : ZMod 39206980188788485360297)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (1993, 1), (191099, 1), (138364521187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (1993, 1), (191099, 1), (138364521187, 1)] : List FactorBlock).map factorBlockValue).prod) = 39206980188788485360297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_31
      · exact prime_eightyFourCD_1993
      · exact prime_eightyFourCD_191099
      · exact prime_eightyFourCD_138364521187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 39206980188788485360297) ^ 19603490094394242680148 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 39206980188788485360297) ^ 13068993396262828453432 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 39206980188788485360297) ^ 1264741296412531785816 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 39206980188788485360297) ^ 19672343295929997672 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 39206980188788485360297) ^ 205165805099914104 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 39206980188788485360297) ^ 283360068408 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_67200664130476790507467 : Nat.Prime 67200664130476790507467 := by
  apply lucas_primality 67200664130476790507467 (2 : ZMod 67200664130476790507467)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11200110688412798417911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11200110688412798417911, 1)] : List FactorBlock).map factorBlockValue).prod) = 67200664130476790507467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_11200110688412798417911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 67200664130476790507467) ^ 33600332065238395253733 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 67200664130476790507467) ^ 22400221376825596835822 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 67200664130476790507467) ^ 6 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_137366407912798882470613 : Nat.Prime 137366407912798882470613 := by
  apply lucas_primality 137366407912798882470613 (2 : ZMod 137366407912798882470613)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (22091, 1), (12807089, 1), (40460709349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (22091, 1), (12807089, 1), (40460709349, 1)] : List FactorBlock).map factorBlockValue).prod) = 137366407912798882470613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_22091
      · exact prime_eightyFourCD_12807089
      · exact prime_eightyFourCD_40460709349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 137366407912798882470613) ^ 68683203956399441235306 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 137366407912798882470613) ^ 45788802637599627490204 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 137366407912798882470613) ^ 6218206867629300732 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 137366407912798882470613) ^ 10725810362745108 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 137366407912798882470613) ^ 3395056837188 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_341928571847863188075259 : Nat.Prime 341928571847863188075259 := by
  apply lucas_primality 341928571847863188075259 (2 : ZMod 341928571847863188075259)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (2719, 1), (2994173031470456471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (2719, 1), (2994173031470456471, 1)] : List FactorBlock).map factorBlockValue).prod) = 341928571847863188075259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_2719
      · exact prime_eightyFourCD_2994173031470456471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 341928571847863188075259) ^ 170964285923931594037629 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 341928571847863188075259) ^ 113976190615954396025086 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 341928571847863188075259) ^ 48846938835409026867894 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 341928571847863188075259) ^ 125755267321759171782 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 341928571847863188075259) ^ 114198 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_627978590671968282320143 : Nat.Prime 627978590671968282320143 := by
  apply lucas_primality 627978590671968282320143 (5 : ZMod 627978590671968282320143)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (1326971, 1), (4151246808484493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (1326971, 1), (4151246808484493, 1)] : List FactorBlock).map factorBlockValue).prod) = 627978590671968282320143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_19
      · exact prime_eightyFourCD_1326971
      · exact prime_eightyFourCD_4151246808484493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 627978590671968282320143) ^ 313989295335984141160071 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 627978590671968282320143) ^ 209326196890656094106714 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 627978590671968282320143) ^ 33051504772208856964218 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 627978590671968282320143) ^ 473242136167232202 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 627978590671968282320143) ^ 151274694 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_628634482425635721878707 : Nat.Prime 628634482425635721878707 := by
  apply lucas_primality 628634482425635721878707 (2 : ZMod 628634482425635721878707)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7482966307, 1), (14001454695793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7482966307, 1), (14001454695793, 1)] : List FactorBlock).map factorBlockValue).prod) = 628634482425635721878707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_7482966307
      · exact prime_eightyFourCD_14001454695793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 628634482425635721878707) ^ 314317241212817860939353 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 628634482425635721878707) ^ 209544827475211907292902 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 628634482425635721878707) ^ 84008728174758 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 628634482425635721878707) ^ 44897797842 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_953303751040432734062437 : Nat.Prime 953303751040432734062437 := by
  apply lucas_primality 953303751040432734062437 (2 : ZMod 953303751040432734062437)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (46819, 1), (138403, 1), (12259772705179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (46819, 1), (138403, 1), (12259772705179, 1)] : List FactorBlock).map factorBlockValue).prod) = 953303751040432734062437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_46819
      · exact prime_eightyFourCD_138403
      · exact prime_eightyFourCD_12259772705179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 953303751040432734062437) ^ 476651875520216367031218 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 953303751040432734062437) ^ 317767917013477578020812 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 953303751040432734062437) ^ 20361471860578669644 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 953303751040432734062437) ^ 6887883579405307212 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 953303751040432734062437) ^ 77758680684 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1136417835936297246460703 : Nat.Prime 1136417835936297246460703 := by
  apply lucas_primality 1136417835936297246460703 (5 : ZMod 1136417835936297246460703)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (79, 1), (157907, 1), (9208417, 1), (706637293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (79, 1), (157907, 1), (9208417, 1), (706637293, 1)] : List FactorBlock).map factorBlockValue).prod) = 1136417835936297246460703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_79
      · exact prime_eightyFourCD_157907
      · exact prime_eightyFourCD_9208417
      · exact prime_eightyFourCD_706637293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1136417835936297246460703) ^ 568208917968148623230351 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1136417835936297246460703) ^ 162345405133756749494386 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1136417835936297246460703) ^ 14385035897927813246338 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1136417835936297246460703) ^ 7196754013034870186 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1136417835936297246460703) ^ 123410770378480606 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1136417835936297246460703) ^ 1608205294560214 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_1270669152267734787744439 : Nat.Prime 1270669152267734787744439 := by
  apply lucas_primality 1270669152267734787744439 (6 : ZMod 1270669152267734787744439)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (33563, 1), (1404831863, 1), (4491548717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (33563, 1), (1404831863, 1), (4491548717, 1)] : List FactorBlock).map factorBlockValue).prod) = 1270669152267734787744439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_33563
      · exact prime_eightyFourCD_1404831863
      · exact prime_eightyFourCD_4491548717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1270669152267734787744439) ^ 635334576133867393872219 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1270669152267734787744439) ^ 423556384089244929248146 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1270669152267734787744439) ^ 37859224511150218626 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1270669152267734787744439) ^ 904499097532026 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 1270669152267734787744439) ^ 282902230907214 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_2417841414633030142449101 : Nat.Prime 2417841414633030142449101 := by
  apply lucas_primality 2417841414633030142449101 (2 : ZMod 2417841414633030142449101)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (43, 1), (794491, 1), (707734513137907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (43, 1), (794491, 1), (707734513137907, 1)] : List FactorBlock).map factorBlockValue).prod) = 2417841414633030142449101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_43
      · exact prime_eightyFourCD_794491
      · exact prime_eightyFourCD_707734513137907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2417841414633030142449101) ^ 1208920707316515071224550 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2417841414633030142449101) ^ 483568282926606028489820 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2417841414633030142449101) ^ 56228870107744887033700 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2417841414633030142449101) ^ 3043258406493000100 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2417841414633030142449101) ^ 3416311300 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_2592487489613832460671793 : Nat.Prime 2592487489613832460671793 := by
  apply lucas_primality 2592487489613832460671793 (5 : ZMod 2592487489613832460671793)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (659, 1), (81957748154205629131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (659, 1), (81957748154205629131, 1)] : List FactorBlock).map factorBlockValue).prod) = 2592487489613832460671793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_659
      · exact prime_eightyFourCD_81957748154205629131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2592487489613832460671793) ^ 1296243744806916230335896 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2592487489613832460671793) ^ 864162496537944153557264 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2592487489613832460671793) ^ 3933971911401870198288 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2592487489613832460671793) ^ 31632 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_4088867682173792822420717 : Nat.Prime 4088867682173792822420717 := by
  apply lucas_primality 4088867682173792822420717 (2 : ZMod 4088867682173792822420717)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (111869, 1), (9137624547850147991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (111869, 1), (9137624547850147991, 1)] : List FactorBlock).map factorBlockValue).prod) = 4088867682173792822420717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_111869
      · exact prime_eightyFourCD_9137624547850147991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4088867682173792822420717) ^ 2044433841086896411210358 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4088867682173792822420717) ^ 36550498191400591964 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4088867682173792822420717) ^ 447476 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_4688655788897459046832273 : Nat.Prime 4688655788897459046832273 := by
  apply lucas_primality 4688655788897459046832273 (10 : ZMod 4688655788897459046832273)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (31, 1), (1615755517, 1), (1950157879457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (31, 1), (1615755517, 1), (1950157879457, 1)] : List FactorBlock).map factorBlockValue).prod) = 4688655788897459046832273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_31
      · exact prime_eightyFourCD_1615755517
      · exact prime_eightyFourCD_1950157879457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 4688655788897459046832273) ^ 2344327894448729523416136 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 4688655788897459046832273) ^ 1562885262965819682277424 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 4688655788897459046832273) ^ 151246960932176098284912 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 4688655788897459046832273) ^ 2901834924632016 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (10 : ZMod 4688655788897459046832273) ^ 2404244209296 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_11266071272222017024498511 : Nat.Prime 11266071272222017024498511 := by
  apply lucas_primality 11266071272222017024498511 (13 : ZMod 11266071272222017024498511)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2118667, 1), (531752808356481553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2118667, 1), (531752808356481553, 1)] : List FactorBlock).map factorBlockValue).prod) = 11266071272222017024498511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_2118667
      · exact prime_eightyFourCD_531752808356481553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 11266071272222017024498511) ^ 5633035636111008512249255 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 11266071272222017024498511) ^ 2253214254444403404899702 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 11266071272222017024498511) ^ 5317528083564815530 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (13 : ZMod 11266071272222017024498511) ^ 21186670 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_13848893915023996663081073 : Nat.Prime 13848893915023996663081073 := by
  apply lucas_primality 13848893915023996663081073 (3 : ZMod 13848893915023996663081073)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (17, 1), (107, 1), (7591, 1), (1183409, 1), (7567118021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (17, 1), (107, 1), (7591, 1), (1183409, 1), (7567118021, 1)] : List FactorBlock).map factorBlockValue).prod) = 13848893915023996663081073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_17
      · exact prime_eightyFourCD_107
      · exact prime_eightyFourCD_7591
      · exact prime_eightyFourCD_1183409
      · exact prime_eightyFourCD_7567118021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13848893915023996663081073) ^ 6924446957511998331540536 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 13848893915023996663081073) ^ 1978413416431999523297296 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 13848893915023996663081073) ^ 814640818530823333122416 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 13848893915023996663081073) ^ 129428915093682211804496 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 13848893915023996663081073) ^ 1824383337508101259792 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 13848893915023996663081073) ^ 11702542329003748208 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 13848893915023996663081073) ^ 1830141128576432 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_16283065791873598962281419 : Nat.Prime 16283065791873598962281419 := by
  apply lucas_primality 16283065791873598962281419 (2 : ZMod 16283065791873598962281419)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (593, 1), (941, 1), (4863406943289134531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (593, 1), (941, 1), (4863406943289134531, 1)] : List FactorBlock).map factorBlockValue).prod) = 16283065791873598962281419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_593
      · exact prime_eightyFourCD_941
      · exact prime_eightyFourCD_4863406943289134531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16283065791873598962281419) ^ 8141532895936799481140709 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16283065791873598962281419) ^ 5427688597291199654093806 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16283065791873598962281419) ^ 27458795601810453562026 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16283065791873598962281419) ^ 17304001904222740661298 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16283065791873598962281419) ^ 3348078 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_60518231727383961042629113 : Nat.Prime 60518231727383961042629113 := by
  apply lucas_primality 60518231727383961042629113 (5 : ZMod 60518231727383961042629113)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (37, 1), (22717053951720706097083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (37, 1), (22717053951720706097083, 1)] : List FactorBlock).map factorBlockValue).prod) = 60518231727383961042629113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_37
      · exact prime_eightyFourCD_22717053951720706097083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 60518231727383961042629113) ^ 30259115863691980521314556 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 60518231727383961042629113) ^ 20172743909127987014209704 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 60518231727383961042629113) ^ 1635627884523890838989976 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 60518231727383961042629113) ^ 2664 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_136228282941888998725588991 : Nat.Prime 136228282941888998725588991 := by
  apply lucas_primality 136228282941888998725588991 (7 : ZMod 136228282941888998725588991)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (7129, 1), (272986159032300660733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (7129, 1), (272986159032300660733, 1)] : List FactorBlock).map factorBlockValue).prod) = 136228282941888998725588991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_7129
      · exact prime_eightyFourCD_272986159032300660733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 136228282941888998725588991) ^ 68114141470944499362794495 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 136228282941888998725588991) ^ 27245656588377799745117798 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 136228282941888998725588991) ^ 19461183277412714103655570 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 136228282941888998725588991) ^ 19109031132261046251310 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (7 : ZMod 136228282941888998725588991) ^ 499030 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_294689668441059584780280043 : Nat.Prime 294689668441059584780280043 := by
  apply lucas_primality 294689668441059584780280043 (2 : ZMod 294689668441059584780280043)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (129893, 1), (90045533, 1), (4199192066903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (129893, 1), (90045533, 1), (4199192066903, 1)] : List FactorBlock).map factorBlockValue).prod) = 294689668441059584780280043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_129893
      · exact prime_eightyFourCD_90045533
      · exact prime_eightyFourCD_4199192066903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 294689668441059584780280043) ^ 147344834220529792390140021 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 294689668441059584780280043) ^ 98229889480353194926760014 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 294689668441059584780280043) ^ 2268710927001913765794 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 294689668441059584780280043) ^ 3272673930877388274 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 294689668441059584780280043) ^ 70177706507814 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_689655682393313056048294267 : Nat.Prime 689655682393313056048294267 := by
  apply lucas_primality 689655682393313056048294267 (2 : ZMod 689655682393313056048294267)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (199, 1), (1666523, 1), (16902959, 1), (20504724677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (199, 1), (1666523, 1), (16902959, 1), (20504724677, 1)] : List FactorBlock).map factorBlockValue).prod) = 689655682393313056048294267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_199
      · exact prime_eightyFourCD_1666523
      · exact prime_eightyFourCD_16902959
      · exact prime_eightyFourCD_20504724677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 689655682393313056048294267) ^ 344827841196656528024147133 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 689655682393313056048294267) ^ 229885227464437685349431422 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 689655682393313056048294267) ^ 3465606444187502794212534 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 689655682393313056048294267) ^ 413829081502813376142 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 689655682393313056048294267) ^ 40800884767768356774 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 689655682393313056048294267) ^ 33633988910219058 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_3009406614079911517301647711 : Nat.Prime 3009406614079911517301647711 := by
  apply lucas_primality 3009406614079911517301647711 (6 : ZMod 3009406614079911517301647711)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (127, 1), (271, 1), (30326687849, 1), (96108461129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (127, 1), (271, 1), (30326687849, 1), (96108461129, 1)] : List FactorBlock).map factorBlockValue).prod) = 3009406614079911517301647711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_127
      · exact prime_eightyFourCD_271
      · exact prime_eightyFourCD_30326687849
      · exact prime_eightyFourCD_96108461129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3009406614079911517301647711) ^ 1504703307039955758650823855 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 3009406614079911517301647711) ^ 1003135538026637172433882570 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 3009406614079911517301647711) ^ 601881322815982303460329542 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 3009406614079911517301647711) ^ 23696115071495366277965730 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 3009406614079911517301647711) ^ 11104821454169415192995010 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 3009406614079911517301647711) ^ 99232947200303790 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (6 : ZMod 3009406614079911517301647711) ^ 31312608470970990 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_3972416730585483202838174977 : Nat.Prime 3972416730585483202838174977 := by
  apply lucas_primality 3972416730585483202838174977 (5 : ZMod 3972416730585483202838174977)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (739, 1), (22283, 1), (314105458523230111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (739, 1), (22283, 1), (314105458523230111, 1)] : List FactorBlock).map factorBlockValue).prod) = 3972416730585483202838174977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_739
      · exact prime_eightyFourCD_22283
      · exact prime_eightyFourCD_314105458523230111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3972416730585483202838174977) ^ 1986208365292741601419087488 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3972416730585483202838174977) ^ 1324138910195161067612724992 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3972416730585483202838174977) ^ 5375394763985768880701184 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3972416730585483202838174977) ^ 178271181195776295958272 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3972416730585483202838174977) ^ 12646761216 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_5226864119191425266892335497 : Nat.Prime 5226864119191425266892335497 := by
  apply lucas_primality 5226864119191425266892335497 (5 : ZMod 5226864119191425266892335497)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (41, 1), (57486973, 1), (13200142826062729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (41, 1), (57486973, 1), (13200142826062729, 1)] : List FactorBlock).map factorBlockValue).prod) = 5226864119191425266892335497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_41
      · exact prime_eightyFourCD_57486973
      · exact prime_eightyFourCD_13200142826062729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5226864119191425266892335497) ^ 2613432059595712633446167748 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 5226864119191425266892335497) ^ 1742288039730475088964111832 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 5226864119191425266892335497) ^ 746694874170203609556047928 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 5226864119191425266892335497) ^ 127484490711985982119325256 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 5226864119191425266892335497) ^ 90922583785920077352 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 5226864119191425266892335497) ^ 395970270024 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_11034490918293008896772708269 : Nat.Prime 11034490918293008896772708269 := by
  apply lucas_primality 11034490918293008896772708269 (2 : ZMod 11034490918293008896772708269)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (71, 1), (4357, 1), (80209, 1), (37059712430045443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (71, 1), (4357, 1), (80209, 1), (37059712430045443, 1)] : List FactorBlock).map factorBlockValue).prod) = 11034490918293008896772708269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_71
      · exact prime_eightyFourCD_4357
      · exact prime_eightyFourCD_80209
      · exact prime_eightyFourCD_37059712430045443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11034490918293008896772708269) ^ 5517245459146504448386354134 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 11034490918293008896772708269) ^ 3678163639431002965590902756 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 11034490918293008896772708269) ^ 155415365046380406996798708 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 11034490918293008896772708269) ^ 2532589148104890726824124 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 11034490918293008896772708269) ^ 137571730333167211868652 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 11034490918293008896772708269) ^ 297748962276 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_12413802283079635008869296807 : Nat.Prime 12413802283079635008869296807 := by
  apply lucas_primality 12413802283079635008869296807 (3 : ZMod 12413802283079635008869296807)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (689655682393313056048294267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (689655682393313056048294267, 1)] : List FactorBlock).map factorBlockValue).prod) = 12413802283079635008869296807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_689655682393313056048294267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 12413802283079635008869296807) ^ 6206901141539817504434648403 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 12413802283079635008869296807) ^ 4137934094359878336289765602 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 12413802283079635008869296807) ^ 18 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_14187202609233868581564910637 : Nat.Prime 14187202609233868581564910637 := by
  apply lucas_primality 14187202609233868581564910637 (3 : ZMod 14187202609233868581564910637)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (17, 1), (79, 1), (34298098387100667679369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (17, 1), (79, 1), (34298098387100667679369, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233868581564910637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_7
      · exact prime_eightyFourCD_11
      · exact prime_eightyFourCD_17
      · exact prime_eightyFourCD_79
      · exact prime_eightyFourCD_34298098387100667679369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14187202609233868581564910637) ^ 7093601304616934290782455318 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 14187202609233868581564910637) ^ 2026743229890552654509272948 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 14187202609233868581564910637) ^ 1289745691748533507414991876 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 14187202609233868581564910637) ^ 834541329954933445974406508 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 14187202609233868581564910637) ^ 179584843154859095969176084 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (3 : ZMod 14187202609233868581564910637) ^ 413644 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_16551736377439513345159062407 : Nat.Prime 16551736377439513345159062407 := by
  apply lucas_primality 16551736377439513345159062407 (5 : ZMod 16551736377439513345159062407)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (457, 1), (102102157, 1), (5721379479820937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (457, 1), (102102157, 1), (5721379479820937, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439513345159062407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_31
      · exact prime_eightyFourCD_457
      · exact prime_eightyFourCD_102102157
      · exact prime_eightyFourCD_5721379479820937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 16551736377439513345159062407) ^ 8275868188719756672579531203 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 16551736377439513345159062407) ^ 533926979917403656295453626 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 16551736377439513345159062407) ^ 36218241526125849770588758 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 16551736377439513345159062407) ^ 162109566181246428958 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 16551736377439513345159062407) ^ 2892962516438 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_19862083652927416014190874899 : Nat.Prime 19862083652927416014190874899 := by
  apply lucas_primality 19862083652927416014190874899 (2 : ZMod 19862083652927416014190874899)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (153749, 1), (21530854024988147363767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (153749, 1), (21530854024988147363767, 1)] : List FactorBlock).map factorBlockValue).prod) = 19862083652927416014190874899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_153749
      · exact prime_eightyFourCD_21530854024988147363767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19862083652927416014190874899) ^ 9931041826463708007095437449 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19862083652927416014190874899) ^ 6620694550975805338063624966 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19862083652927416014190874899) ^ 129185124149928884182602 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19862083652927416014190874899) ^ 922494 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_24827604566159270017738593623 : Nat.Prime 24827604566159270017738593623 := by
  apply lucas_primality 24827604566159270017738593623 (5 : ZMod 24827604566159270017738593623)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6199399, 1), (2002420280269044629789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6199399, 1), (2002420280269044629789, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159270017738593623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_6199399
      · exact prime_eightyFourCD_2002420280269044629789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 24827604566159270017738593623) ^ 12413802283079635008869296811 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 24827604566159270017738593623) ^ 4004840560538089259578 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (5 : ZMod 24827604566159270017738593623) ^ 12398798 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_99310418264637080070954374437 : Nat.Prime 99310418264637080070954374437 := by
  apply lucas_primality 99310418264637080070954374437 (2 : ZMod 99310418264637080070954374437)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (457, 1), (102102157, 1), (5721379479820937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (457, 1), (102102157, 1), (5721379479820937, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_31
      · exact prime_eightyFourCD_457
      · exact prime_eightyFourCD_102102157
      · exact prime_eightyFourCD_5721379479820937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 99310418264637080070954374437) ^ 49655209132318540035477187218 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 99310418264637080070954374437) ^ 33103472754879026690318124812 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 99310418264637080070954374437) ^ 3203561879504421937772721756 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 99310418264637080070954374437) ^ 217309449156755098623532548 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 99310418264637080070954374437) ^ 972657397087478573748 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 99310418264637080070954374437) ^ 17357775098628 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem prime_eightyFourCD_99310418264637080070954374461 : Nat.Prime 99310418264637080070954374461 := by
  apply lucas_primality 99310418264637080070954374461 (2 : ZMod 99310418264637080070954374461)
  · rw [← eightyFourCDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (73, 1), (1945728377, 1), (11653019889088321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (73, 1), (1945728377, 1), (11653019889088321, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyFourCD_2
      · exact prime_eightyFourCD_3
      · exact prime_eightyFourCD_5
      · exact prime_eightyFourCD_73
      · exact prime_eightyFourCD_1945728377
      · exact prime_eightyFourCD_11653019889088321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 99310418264637080070954374461) ^ 49655209132318540035477187230 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 99310418264637080070954374461) ^ 33103472754879026690318124820 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 99310418264637080070954374461) ^ 19862083652927416014190874892 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 99310418264637080070954374461) ^ 1360416688556672329739101020 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 99310418264637080070954374461) ^ 51040227114206845980 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide
    · change (2 : ZMod 99310418264637080070954374461) ^ 8522290291260 ≠ 1
      rw [← eightyFourCDFastPow_eq_pow]
      decide

private theorem phi_eightyFourCD_99310418264637080070954374400 : Nat.totient 99310418264637080070954374400 = 26445755372488625272487731200 := by
  rw [← show ((([(2, 8), (3, 1), (5, 2), (739, 1), (22283, 1), (314105458523230111, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_3, prime_eightyFourCD_5, prime_eightyFourCD_739, prime_eightyFourCD_22283, prime_eightyFourCD_314105458523230111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374401 : Nat.totient 99310418264637080070954374401 = 92719899965219968569125437440 := by
  rw [← show ((([(17, 1), (131, 1), (2633, 1), (1162074659, 1), (14574367091329, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_17, prime_eightyFourCD_131, prime_eightyFourCD_2633, prime_eightyFourCD_1162074659, prime_eightyFourCD_14574367091329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374402 : Nat.totient 99310418264637080070954374402 = 48873601072636687993824460800 := by
  rw [← show ((([(2, 1), (149, 1), (193, 1), (421, 1), (643, 1), (540383, 1), (2032711, 1), (5806987, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_149, prime_eightyFourCD_193, prime_eightyFourCD_421, prime_eightyFourCD_643, prime_eightyFourCD_540383, prime_eightyFourCD_2032711, prime_eightyFourCD_5806987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374403 : Nat.totient 99310418264637080070954374403 = 55482113139075697921772470272 := by
  rw [← show ((([(3, 2), (7, 2), (47, 1), (937, 1), (1489657409, 1), (3432672507533, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_3, prime_eightyFourCD_7, prime_eightyFourCD_47, prime_eightyFourCD_937, prime_eightyFourCD_1489657409, prime_eightyFourCD_3432672507533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374404 : Nat.totient 99310418264637080070954374404 = 46842587361370836602966310912 := by
  rw [← show ((([(2, 2), (23, 1), (109, 1), (269, 1), (1097, 1), (184913, 1), (3447443, 1), (52644989, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_23, prime_eightyFourCD_109, prime_eightyFourCD_269, prime_eightyFourCD_1097, prime_eightyFourCD_184913, prime_eightyFourCD_3447443, prime_eightyFourCD_52644989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374405 : Nat.totient 99310418264637080070954374405 = 72770740258560058331337427200 := by
  rw [← show ((([(5, 1), (19, 1), (31, 1), (1087, 1), (64327, 1), (482266027735322221, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_5, prime_eightyFourCD_19, prime_eightyFourCD_31, prime_eightyFourCD_1087, prime_eightyFourCD_64327, prime_eightyFourCD_482266027735322221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374406 : Nat.totient 99310418264637080070954374406 = 30100190413993089728108614272 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (67, 1), (38299, 1), (2280632647, 1), (217561795427, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_3, prime_eightyFourCD_13, prime_eightyFourCD_67, prime_eightyFourCD_38299, prime_eightyFourCD_2280632647, prime_eightyFourCD_217561795427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374407 : Nat.totient 99310418264637080070954374407 = 99310357354583615024404132800 := by
  rw [← show ((([(1632569, 1), (1252523653, 1), (48566558456051, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_1632569, prime_eightyFourCD_1252523653, prime_eightyFourCD_48566558456051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374408 : Nat.totient 99310418264637080070954374408 = 45128198065803241012134508800 := by
  rw [← show ((([(2, 3), (11, 1), (3499, 1), (18536890189, 1), (17399281684781, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_11, prime_eightyFourCD_3499, prime_eightyFourCD_18536890189, prime_eightyFourCD_17399281684781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374409 : Nat.totient 99310418264637080070954374409 = 66162218895328992311778739200 := by
  rw [← show ((([(3, 1), (1483, 1), (800161, 1), (27896840881203395081, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_3, prime_eightyFourCD_1483, prime_eightyFourCD_800161, prime_eightyFourCD_27896840881203395081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374410 : Nat.totient 99310418264637080070954374410 = 34038675702013994829641521152 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (3209, 1), (88911631663, 1), (4972427659889, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_5, prime_eightyFourCD_7, prime_eightyFourCD_3209, prime_eightyFourCD_88911631663, prime_eightyFourCD_4972427659889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374411 : Nat.totient 99310418264637080070954374411 = 95885920944678789924115390848 := by
  rw [← show ((([(29, 1), (692721847, 1), (4943538588207987697, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_29, prime_eightyFourCD_692721847, prime_eightyFourCD_4943538588207987697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374412 : Nat.totient 99310418264637080070954374412 = 32629329094194134670798904320 := by
  rw [← show ((([(2, 2), (3, 3), (71, 1), (4357, 1), (80209, 1), (37059712430045443, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_3, prime_eightyFourCD_71, prime_eightyFourCD_4357, prime_eightyFourCD_80209, prime_eightyFourCD_37059712430045443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374413 : Nat.totient 99310418264637080070954374413 = 97355248800666839648425295808 := by
  rw [← show ((([(59, 1), (359, 1), (4688655788897459046832273, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_59, prime_eightyFourCD_359, prime_eightyFourCD_4688655788897459046832273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374414 : Nat.totient 99310418264637080070954374414 = 49539277930234031542855193344 := by
  rw [← show ((([(2, 1), (503, 1), (2879, 1), (74697500399, 1), (459038483489, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_503, prime_eightyFourCD_2879, prime_eightyFourCD_74697500399, prime_eightyFourCD_459038483489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374415 : Nat.totient 99310418264637080070954374415 = 52965556407788859743854164000 := by
  rw [← show ((([(3, 1), (5, 1), (3016462917551, 1), (2194853618936911, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_3, prime_eightyFourCD_5, prime_eightyFourCD_3016462917551, prime_eightyFourCD_2194853618936911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374416 : Nat.totient 99310418264637080070954374416 = 48717309127158588609434152320 := by
  rw [← show ((([(2, 4), (53, 1), (48271, 1), (2426122149804315300227, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_53, prime_eightyFourCD_48271, prime_eightyFourCD_2426122149804315300227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374417 : Nat.totient 99310418264637080070954374417 = 85120132883823296144124673536 := by
  rw [← show ((([(7, 1), (47969, 1), (65239, 1), (24589739, 1), (184363477619, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_7, prime_eightyFourCD_47969, prime_eightyFourCD_65239, prime_eightyFourCD_24589739, prime_eightyFourCD_184363477619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374418 : Nat.totient 99310418264637080070954374418 = 31156200553510192957462003200 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (3424459, 1), (284316895490379362201, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_3, prime_eightyFourCD_17, prime_eightyFourCD_3424459, prime_eightyFourCD_284316895490379362201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374419 : Nat.totient 99310418264637080070954374419 = 83113988470340792323991224320 := by
  rw [← show ((([(11, 1), (13, 2), (373, 1), (109967489, 1), (1302393682573453, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_11, prime_eightyFourCD_13, prime_eightyFourCD_373, prime_eightyFourCD_109967489, prime_eightyFourCD_1302393682573453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374420 : Nat.totient 99310418264637080070954374420 = 38650519516239394989114599424 := by
  rw [← show ((([(2, 2), (5, 1), (37, 1), (1788229, 1), (1218456053, 1), (61592819909, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_5, prime_eightyFourCD_37, prime_eightyFourCD_1788229, prime_eightyFourCD_1218456053, prime_eightyFourCD_61592819909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374421 : Nat.totient 99310418264637080070954374421 = 66206945509758053380636249608 := by
  rw [← show ((([(3, 2), (11034490918293008896772708269, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_3, prime_eightyFourCD_11034490918293008896772708269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374422 : Nat.totient 99310418264637080070954374422 = 48454810749555122860319223936 := by
  rw [← show ((([(2, 1), (43, 1), (1063, 1), (617540423, 1), (1759129065237073, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_43, prime_eightyFourCD_1063, prime_eightyFourCD_617540423, prime_eightyFourCD_1759129065237073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374423 : Nat.totient 99310418264637080070954374423 = 99303007648384277974524641760 := by
  rw [← show ((([(13597, 1), (930079, 1), (7852932686361389021, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_13597, prime_eightyFourCD_930079, prime_eightyFourCD_7852932686361389021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374424 : Nat.totient 99310418264637080070954374424 = 26225380490268749694783528960 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (19, 1), (41, 1), (57486973, 1), (13200142826062729, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_3, prime_eightyFourCD_7, prime_eightyFourCD_19, prime_eightyFourCD_41, prime_eightyFourCD_57486973, prime_eightyFourCD_13200142826062729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374425 : Nat.totient 99310418264637080070954374425 = 79448334611709664056763499520 := by
  rw [← show ((([(5, 2), (3972416730585483202838174977, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_5, prime_eightyFourCD_3972416730585483202838174977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374426 : Nat.totient 99310418264637080070954374426 = 49655000629834749311999642208 := by
  rw [← show ((([(2, 1), (248323, 1), (5814199, 1), (34392043143319369, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_248323, prime_eightyFourCD_5814199, prime_eightyFourCD_34392043143319369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374427 : Nat.totient 99310418264637080070954374427 = 63303525438268329749949004800 := by
  rw [← show ((([(3, 1), (23, 1), (2551, 1), (2079433, 1), (34256213, 1), (7920470477, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_3, prime_eightyFourCD_23, prime_eightyFourCD_2551, prime_eightyFourCD_2079433, prime_eightyFourCD_34256213, prime_eightyFourCD_7920470477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374428 : Nat.totient 99310418264637080070954374428 = 49143093067101738170911850496 := by
  rw [← show ((([(2, 2), (97, 1), (285377, 1), (1424939, 1), (629430587940277, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_97, prime_eightyFourCD_285377, prime_eightyFourCD_1424939, prime_eightyFourCD_629430587940277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374429 : Nat.totient 99310418264637080070954374429 = 99303789766426606040303687040 := by
  rw [← show ((([(20393, 1), (56467, 1), (7412773091, 1), (11634246749, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_20393, prime_eightyFourCD_56467, prime_eightyFourCD_7412773091, prime_eightyFourCD_11634246749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374430 : Nat.totient 99310418264637080070954374430 = 23797544935713729846227251200 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (11, 1), (127, 1), (271, 1), (30326687849, 1), (96108461129, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_3, prime_eightyFourCD_5, prime_eightyFourCD_11, prime_eightyFourCD_127, prime_eightyFourCD_271, prime_eightyFourCD_30326687849, prime_eightyFourCD_96108461129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374431 : Nat.totient 99310418264637080070954374431 = 83875614663671144048583763200 := by
  rw [← show ((([(7, 1), (89, 1), (317, 1), (3271, 1), (153732948943606501171, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_7, prime_eightyFourCD_89, prime_eightyFourCD_317, prime_eightyFourCD_3271, prime_eightyFourCD_153732948943606501171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374432 : Nat.totient 99310418264637080070954374432 = 45835577629117956804885361920 := by
  rw [← show ((([(2, 5), (13, 1), (1455847711, 1), (163977980099527507, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_13, prime_eightyFourCD_1455847711, prime_eightyFourCD_163977980099527507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374433 : Nat.totient 99310418264637080070954374433 = 66085909046303285458550990304 := by
  rw [← show ((([(3, 1), (547, 1), (60518231727383961042629113, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_3, prime_eightyFourCD_547, prime_eightyFourCD_60518231727383961042629113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374434 : Nat.totient 99310418264637080070954374434 = 48851694334100600255302211712 := by
  rw [← show ((([(2, 1), (83, 1), (239, 1), (1052451977, 1), (2378408968073533, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_83, prime_eightyFourCD_239, prime_eightyFourCD_1052451977, prime_eightyFourCD_2378408968073533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374435 : Nat.totient 99310418264637080070954374435 = 74723227337556857972255219712 := by
  rw [← show ((([(5, 1), (17, 1), (1447, 1), (6128287609, 1), (131755336656857, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_5, prime_eightyFourCD_17, prime_eightyFourCD_1447, prime_eightyFourCD_6128287609, prime_eightyFourCD_131755336656857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374436 : Nat.totient 99310418264637080070954374436 = 31965518659661697977920235520 := by
  rw [← show ((([(2, 2), (3, 1), (31, 1), (457, 1), (102102157, 1), (5721379479820937, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_3, prime_eightyFourCD_31, prime_eightyFourCD_457, prime_eightyFourCD_102102157, prime_eightyFourCD_5721379479820937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374437 : Nat.totient 99310418264637080070954374437 = 99310418264637080070954374436 := by
  rw [← show ((([(99310418264637080070954374437, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_99310418264637080070954374437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374438 : Nat.totient 99310418264637080070954374438 = 42524661679887856757592114720 := by
  rw [← show ((([(2, 1), (7, 1), (1163, 1), (121591, 1), (3863079383, 1), (12985300303, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_7, prime_eightyFourCD_1163, prime_eightyFourCD_121591, prime_eightyFourCD_3863079383, prime_eightyFourCD_12985300303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374439 : Nat.totient 99310418264637080070954374439 = 66206945509758053380636249140 := by
  rw [← show ((([(3, 6), (136228282941888998725588991, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_3, prime_eightyFourCD_136228282941888998725588991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374440 : Nat.totient 99310418264637080070954374440 = 38351446888284796004694144000 := by
  rw [← show ((([(2, 3), (5, 1), (29, 1), (13291, 1), (1134271, 1), (20687839, 1), (274503071, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_5, prime_eightyFourCD_29, prime_eightyFourCD_13291, prime_eightyFourCD_1134271, prime_eightyFourCD_20687839, prime_eightyFourCD_274503071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374441 : Nat.totient 99310418264637080070954374441 = 88802144126326742752172563200 := by
  rw [← show ((([(11, 1), (61, 1), (4864177, 1), (30427265284783672423, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_11, prime_eightyFourCD_61, prime_eightyFourCD_4864177, prime_eightyFourCD_30427265284783672423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374442 : Nat.totient 99310418264637080070954374442 = 33103472754879026690318124812 := by
  rw [← show ((([(2, 1), (3, 1), (16551736377439513345159062407, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_3, prime_eightyFourCD_16551736377439513345159062407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374443 : Nat.totient 99310418264637080070954374443 = 94083554145445654804062038928 := by
  rw [← show ((([(19, 1), (5226864119191425266892335497, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_19, prime_eightyFourCD_5226864119191425266892335497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374444 : Nat.totient 99310418264637080070954374444 = 49338181057744075440810028032 := by
  rw [← show ((([(2, 2), (157, 1), (65617, 1), (52817077, 1), (45629365929947, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_157, prime_eightyFourCD_65617, prime_eightyFourCD_52817077, prime_eightyFourCD_45629365929947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374445 : Nat.totient 99310418264637080070954374445 = 41902659805103114222127366144 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (13, 1), (10093, 1), (21068717, 1), (342139957225553, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_3, prime_eightyFourCD_5, prime_eightyFourCD_7, prime_eightyFourCD_13, prime_eightyFourCD_10093, prime_eightyFourCD_21068717, prime_eightyFourCD_342139957225553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374446 : Nat.totient 99310418264637080070954374446 = 49654580497836114399755229528 := by
  rw [← show ((([(2, 1), (78989, 1), (628634482425635721878707, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_78989, prime_eightyFourCD_628634482425635721878707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374447 : Nat.totient 99310418264637080070954374447 = 98630055492096630554788032000 := by
  rw [← show ((([(229, 1), (401, 1), (840181, 1), (1287188348581953703, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_229, prime_eightyFourCD_401, prime_eightyFourCD_840181, prime_eightyFourCD_1287188348581953703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374448 : Nat.totient 99310418264637080070954374448 = 33103472754879026690318124768 := by
  rw [← show ((([(2, 4), (3, 2), (689655682393313056048294267, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_3, prime_eightyFourCD_689655682393313056048294267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374449 : Nat.totient 99310418264637080070954374449 = 99309790286046408102671896164 := by
  rw [← show ((([(158143, 1), (627978590671968282320143, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_158143, prime_eightyFourCD_627978590671968282320143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374450 : Nat.totient 99310418264637080070954374450 = 37188521809053141147520680000 := by
  rw [← show ((([(2, 1), (5, 2), (23, 1), (47, 1), (616219, 1), (2981700566578430251, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_5, prime_eightyFourCD_23, prime_eightyFourCD_47, prime_eightyFourCD_616219, prime_eightyFourCD_2981700566578430251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374451 : Nat.totient 99310418264637080070954374451 = 65621043337105327244524399104 := by
  rw [← show ((([(3, 1), (113, 2), (2592487489613832460671793, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_3, prime_eightyFourCD_113, prime_eightyFourCD_2592487489613832460671793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374452 : Nat.totient 99310418264637080070954374452 = 35955382501165371941635061760 := by
  rw [← show ((([(2, 2), (7, 2), (11, 1), (17, 1), (79, 1), (34298098387100667679369, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_7, prime_eightyFourCD_11, prime_eightyFourCD_17, prime_eightyFourCD_79, prime_eightyFourCD_34298098387100667679369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374453 : Nat.totient 99310418264637080070954374453 = 98801303894222099110577012880 := by
  rw [← show ((([(197, 1), (19759, 1), (25513123047606161882911, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_197, prime_eightyFourCD_19759, prime_eightyFourCD_25513123047606161882911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374454 : Nat.totient 99310418264637080070954374454 = 32948580630885613669193036544 := by
  rw [← show ((([(2, 1), (3, 1), (227, 1), (3637, 1), (403450367, 1), (49691749531273, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_3, prime_eightyFourCD_227, prime_eightyFourCD_3637, prime_eightyFourCD_403450367, prime_eightyFourCD_49691749531273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374455 : Nat.totient 99310418264637080070954374455 = 79448333967732276265733879040 := by
  rw [← show ((([(5, 1), (142389881, 1), (929386597, 1), (150089141863, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_5, prime_eightyFourCD_142389881, prime_eightyFourCD_929386597, prime_eightyFourCD_150089141863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374456 : Nat.totient 99310418264637080070954374456 = 49655209132318540035477187224 := by
  rw [← show ((([(2, 3), (12413802283079635008869296807, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_12413802283079635008869296807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374457 : Nat.totient 99310418264637080070954374457 = 63990907490705341836845520000 := by
  rw [← show ((([(3, 2), (37, 1), (151, 1), (1169879, 1), (1688234165419289101, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_3, prime_eightyFourCD_37, prime_eightyFourCD_151, prime_eightyFourCD_1169879, prime_eightyFourCD_1688234165419289101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374458 : Nat.totient 99310418264637080070954374458 = 45830125628253138901507660800 := by
  rw [← show ((([(2, 1), (13, 1), (8747, 1), (263401, 1), (1209577, 1), (1370602112707, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_13, prime_eightyFourCD_8747, prime_eightyFourCD_263401, prime_eightyFourCD_1209577, prime_eightyFourCD_1370602112707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374459 : Nat.totient 99310418264637080070954374459 = 85123215655403211489389463816 := by
  rw [← show ((([(7, 1), (14187202609233868581564910637, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_7, prime_eightyFourCD_14187202609233868581564910637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374460 : Nat.totient 99310418264637080070954374460 = 26120000406863827577281904640 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (73, 1), (1945728377, 1), (11653019889088321, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_3, prime_eightyFourCD_5, prime_eightyFourCD_73, prime_eightyFourCD_1945728377, prime_eightyFourCD_11653019889088321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374461 : Nat.totient 99310418264637080070954374461 = 99310418264637080070954374460 := by
  rw [← show ((([(99310418264637080070954374461, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_99310418264637080070954374461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374462 : Nat.totient 99310418264637080070954374462 = 47041762114434257855554480128 := by
  rw [← show ((([(2, 1), (19, 1), (3145633, 1), (17712609709, 1), (46905158617, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_19, prime_eightyFourCD_3145633, prime_eightyFourCD_17712609709, prime_eightyFourCD_46905158617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374463 : Nat.totient 99310418264637080070954374463 = 60188132281598230346032954200 := by
  rw [← show ((([(3, 1), (11, 1), (3009406614079911517301647711, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_3, prime_eightyFourCD_11, prime_eightyFourCD_3009406614079911517301647711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374464 : Nat.totient 99310418264637080070954374464 = 49654192644560234275077120000 := by
  rw [← show ((([(2, 6), (53401, 1), (573161, 1), (50697765176933141, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_53401, prime_eightyFourCD_573161, prime_eightyFourCD_50697765176933141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374465 : Nat.totient 99310418264637080070954374465 = 75707998949331954404629987200 := by
  rw [← show ((([(5, 1), (41, 1), (43, 1), (11266071272222017024498511, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_5, prime_eightyFourCD_41, prime_eightyFourCD_43, prime_eightyFourCD_11266071272222017024498511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374466 : Nat.totient 99310418264637080070954374466 = 28370170864607348006710185600 := by
  rw [← show ((([(2, 1), (3, 3), (7, 1), (6701, 1), (39206980188788485360297, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_3, prime_eightyFourCD_7, prime_eightyFourCD_6701, prime_eightyFourCD_39206980188788485360297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374467 : Nat.totient 99310418264637080070954374467 = 96072763850054569215787747080 := by
  rw [← show ((([(31, 1), (2819, 1), (1136417835936297246460703, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_31, prime_eightyFourCD_2819, prime_eightyFourCD_1136417835936297246460703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374468 : Nat.totient 99310418264637080070954374468 = 49606575215643469480823251200 := by
  rw [← show ((([(2, 2), (1021, 1), (2558910217, 1), (9502853395587581, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_1021, prime_eightyFourCD_2558910217, prime_eightyFourCD_9502853395587581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374469 : Nat.totient 99310418264637080070954374469 = 58455458009585659805533470720 := by
  rw [← show ((([(3, 1), (17, 1), (29, 1), (53, 1), (103, 1), (3540544289, 1), (3474109568161, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_3, prime_eightyFourCD_17, prime_eightyFourCD_29, prime_eightyFourCD_53, prime_eightyFourCD_103, prime_eightyFourCD_3540544289, prime_eightyFourCD_3474109568161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374470 : Nat.totient 99310418264637080070954374470 = 39724167264057757490499904000 := by
  rw [← show ((([(2, 1), (5, 1), (950405447, 1), (10449268633520056001, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_5, prime_eightyFourCD_950405447, prime_eightyFourCD_10449268633520056001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374471 : Nat.totient 99310418264637080070954374471 = 91639001279441831301834271200 := by
  rw [← show ((([(13, 1), (2851, 1), (14727527099, 1), (181938416650483, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_13, prime_eightyFourCD_2851, prime_eightyFourCD_14727527099, prime_eightyFourCD_181938416650483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374472 : Nat.totient 99310418264637080070954374472 = 32456103380174271953249729280 := by
  rw [← show ((([(2, 3), (3, 1), (59, 1), (383, 1), (24469, 1), (7483703328738025771, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_3, prime_eightyFourCD_59, prime_eightyFourCD_383, prime_eightyFourCD_24469, prime_eightyFourCD_7483703328738025771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374473 : Nat.totient 99310418264637080070954374473 = 79621497283041076650541955712 := by
  rw [← show ((([(7, 1), (23, 1), (67, 1), (137, 1), (67200664130476790507467, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_7, prime_eightyFourCD_23, prime_eightyFourCD_67, prime_eightyFourCD_137, prime_eightyFourCD_67200664130476790507467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374474 : Nat.totient 99310418264637080070954374474 = 45116920797052342458100206000 := by
  rw [← show ((([(2, 1), (11, 1), (1867, 1), (2417841414633030142449101, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_11, prime_eightyFourCD_1867, prime_eightyFourCD_2417841414633030142449101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374475 : Nat.totient 99310418264637080070954374475 = 52851159957681590776421451840 := by
  rw [← show ((([(3, 2), (5, 2), (463, 1), (953303751040432734062437, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_3, prime_eightyFourCD_5, prime_eightyFourCD_463, prime_eightyFourCD_953303751040432734062437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374476 : Nat.totient 99310418264637080070954374476 = 49655196091254818132145656832 := by
  rw [← show ((([(2, 2), (6388337, 1), (9425329, 1), (412335268310003, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_6388337, prime_eightyFourCD_9425329, prime_eightyFourCD_412335268310003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374477 : Nat.totient 99310418264637080070954374477 = 99310418264039503549764051036 := by
  rw [← show ((([(166188667663, 1), (597576355001655779, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_166188667663, prime_eightyFourCD_597576355001655779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374478 : Nat.totient 99310418264637080070954374478 = 33102788897735330963941877496 := by
  rw [← show ((([(2, 1), (3, 1), (48407, 1), (341928571847863188075259, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_3, prime_eightyFourCD_48407, prime_eightyFourCD_341928571847863188075259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374479 : Nat.totient 99310418264637080070954374479 = 99310400169737452391003100120 := by
  rw [← show ((([(5490883, 1), (11802392531, 1), (1532436778823, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_5490883, prime_eightyFourCD_11802392531, prime_eightyFourCD_1532436778823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374480 : Nat.totient 99310418264637080070954374480 = 34022911911842027210321180160 := by
  rw [← show ((([(2, 4), (5, 1), (7, 1), (1291, 1), (137366407912798882470613, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_5, prime_eightyFourCD_7, prime_eightyFourCD_1291, prime_eightyFourCD_137366407912798882470613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374481 : Nat.totient 99310418264637080070954374481 = 62136179061789653640065891088 := by
  rw [← show ((([(3, 1), (19, 1), (107, 1), (16283065791873598962281419, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_3, prime_eightyFourCD_19, prime_eightyFourCD_107, prime_eightyFourCD_16283065791873598962281419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374482 : Nat.totient 99310418264637080070954374482 = 49651283305702128510678286080 := by
  rw [← show ((([(2, 1), (12703, 1), (3059341, 1), (75382193, 1), (16949694019, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_12703, prime_eightyFourCD_3059341, prime_eightyFourCD_75382193, prime_eightyFourCD_16949694019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374483 : Nat.totient 99310418264637080070954374483 = 96942257405167976641567504000 := by
  rw [← show ((([(71, 1), (101, 1), (13848893915023996663081073, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_71, prime_eightyFourCD_101, prime_eightyFourCD_13848893915023996663081073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374484 : Nat.totient 99310418264637080070954374484 = 30374075415807932366243045952 := by
  rw [← show ((([(2, 2), (3, 2), (13, 1), (167, 1), (1270669152267734787744439, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_3, prime_eightyFourCD_13, prime_eightyFourCD_167, prime_eightyFourCD_1270669152267734787744439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374485 : Nat.totient 99310418264637080070954374485 = 72097339479431566694604302400 := by
  rw [← show ((([(5, 1), (11, 3), (743, 1), (2311, 1), (8690764705513186619, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_5, prime_eightyFourCD_11, prime_eightyFourCD_743, prime_eightyFourCD_2311, prime_eightyFourCD_8690764705513186619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374486 : Nat.totient 99310418264637080070954374486 = 46308409398086437458778521600 := by
  rw [← show ((([(2, 1), (17, 1), (257, 1), (331, 1), (449, 1), (917003, 1), (83394551885971, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_17, prime_eightyFourCD_257, prime_eightyFourCD_331, prime_eightyFourCD_449, prime_eightyFourCD_917003, prime_eightyFourCD_83394551885971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374487 : Nat.totient 99310418264637080070954374487 = 56431759924758230904961611360 := by
  rw [← show ((([(3, 1), (7, 1), (179, 1), (3126131, 1), (8451140311072988803, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_3, prime_eightyFourCD_7, prime_eightyFourCD_179, prime_eightyFourCD_3126131, prime_eightyFourCD_8451140311072988803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374488 : Nat.totient 99310418264637080070954374488 = 49655201122637418959273870496 := by
  rw [← show ((([(2, 3), (6199399, 1), (2002420280269044629789, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_6199399, prime_eightyFourCD_2002420280269044629789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374489 : Nat.totient 99310418264637080070954374489 = 99310418264548578588463427124 := by
  rw [← show ((([(1122147049783, 1), (88500360343897583, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_1122147049783, prime_eightyFourCD_88500360343897583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374490 : Nat.totient 99310418264637080070954374490 = 26482605957071021447074359744 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (153749, 1), (21530854024988147363767, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_3, prime_eightyFourCD_5, prime_eightyFourCD_153749, prime_eightyFourCD_21530854024988147363767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374491 : Nat.totient 99310418264637080070954374491 = 99015728596196020486174094112 := by
  rw [← show ((([(337, 1), (294689668441059584780280043, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_337, prime_eightyFourCD_294689668441059584780280043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374492 : Nat.totient 99310418264637080070954374492 = 49655209132318540035477187244 := by
  rw [← show ((([(2, 2), (24827604566159270017738593623, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_24827604566159270017738593623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374493 : Nat.totient 99310418264637080070954374493 = 66206851888294813261030574688 := by
  rw [← show ((([(3, 3), (707177, 1), (5201192402228866274767, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_3, prime_eightyFourCD_707177, prime_eightyFourCD_5201192402228866274767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374494 : Nat.totient 99310418264637080070954374494 = 41315687466761626023043754496 := by
  rw [← show ((([(2, 1), (7, 1), (37, 1), (509, 1), (3517, 1), (16547, 1), (6472255209000863, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_7, prime_eightyFourCD_37, prime_eightyFourCD_509, prime_eightyFourCD_3517, prime_eightyFourCD_16547, prime_eightyFourCD_6472255209000863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374495 : Nat.totient 99310418264637080070954374495 = 79448334611709664056763499592 := by
  rw [← show ((([(5, 1), (19862083652927416014190874899, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_5, prime_eightyFourCD_19862083652927416014190874899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374496 : Nat.totient 99310418264637080070954374496 = 28785628482503501469841840640 := by
  rw [← show ((([(2, 5), (3, 1), (11, 1), (23, 1), (4088867682173792822420717, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_3, prime_eightyFourCD_11, prime_eightyFourCD_23, prime_eightyFourCD_4088867682173792822420717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374497 : Nat.totient 99310418264637080070954374497 = 89392704456304255918073315328 := by
  rw [← show ((([(13, 1), (47, 1), (347, 1), (1303, 1), (119447, 1), (2744257, 1), (1096679393, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_13, prime_eightyFourCD_47, prime_eightyFourCD_347, prime_eightyFourCD_1303, prime_eightyFourCD_119447, prime_eightyFourCD_2744257, prime_eightyFourCD_1096679393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374498 : Nat.totient 99310418264637080070954374498 = 46197287063507200741016762880 := by
  rw [← show ((([(2, 1), (29, 1), (31, 1), (233, 1), (366899293, 1), (646103848179679, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_29, prime_eightyFourCD_31, prime_eightyFourCD_233, prime_eightyFourCD_366899293, prime_eightyFourCD_646103848179679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374499 : Nat.totient 99310418264637080070954374499 = 66082243551254020576379836800 := by
  rw [← show ((([(3, 1), (541, 1), (28447, 1), (1213780949, 1), (1772146011871, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_3, prime_eightyFourCD_541, prime_eightyFourCD_28447, prime_eightyFourCD_1213780949, prime_eightyFourCD_1772146011871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374500 : Nat.totient 99310418264637080070954374500 = 37632101134059901821965875200 := by
  rw [← show ((([(2, 2), (5, 3), (19, 1), (28499, 1), (6041178673, 1), (60718341973, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_2, prime_eightyFourCD_5, prime_eightyFourCD_19, prime_eightyFourCD_28499, prime_eightyFourCD_6041178673, prime_eightyFourCD_60718341973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyFourCD_99310418264637080070954374501 : Nat.totient 99310418264637080070954374501 = 85001911455649618752228799200 := by
  rw [← show ((([(7, 2), (991, 1), (2423, 1), (272411, 1), (3098468047290263, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637080070954374501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyFourCD_7, prime_eightyFourCD_991, prime_eightyFourCD_2423, prime_eightyFourCD_272411, prime_eightyFourCD_3098468047290263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64EightyFourCD : certifiedKill 1 99310418264637080070954374399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_eightyFourCD_99310418264637080070954374400, phi_eightyFourCD_99310418264637080070954374401, phi_eightyFourCD_99310418264637080070954374402,
    phi_eightyFourCD_99310418264637080070954374403, phi_eightyFourCD_99310418264637080070954374404, phi_eightyFourCD_99310418264637080070954374405,
    phi_eightyFourCD_99310418264637080070954374406, phi_eightyFourCD_99310418264637080070954374407, phi_eightyFourCD_99310418264637080070954374408,
    phi_eightyFourCD_99310418264637080070954374409, phi_eightyFourCD_99310418264637080070954374410, phi_eightyFourCD_99310418264637080070954374411,
    phi_eightyFourCD_99310418264637080070954374412, phi_eightyFourCD_99310418264637080070954374413, phi_eightyFourCD_99310418264637080070954374414,
    phi_eightyFourCD_99310418264637080070954374415, phi_eightyFourCD_99310418264637080070954374416, phi_eightyFourCD_99310418264637080070954374417,
    phi_eightyFourCD_99310418264637080070954374418, phi_eightyFourCD_99310418264637080070954374419, phi_eightyFourCD_99310418264637080070954374420,
    phi_eightyFourCD_99310418264637080070954374421, phi_eightyFourCD_99310418264637080070954374422, phi_eightyFourCD_99310418264637080070954374423,
    phi_eightyFourCD_99310418264637080070954374424, phi_eightyFourCD_99310418264637080070954374425, phi_eightyFourCD_99310418264637080070954374426,
    phi_eightyFourCD_99310418264637080070954374427, phi_eightyFourCD_99310418264637080070954374428, phi_eightyFourCD_99310418264637080070954374429,
    phi_eightyFourCD_99310418264637080070954374430, phi_eightyFourCD_99310418264637080070954374431, phi_eightyFourCD_99310418264637080070954374432,
    phi_eightyFourCD_99310418264637080070954374433, phi_eightyFourCD_99310418264637080070954374434, phi_eightyFourCD_99310418264637080070954374435,
    phi_eightyFourCD_99310418264637080070954374436, phi_eightyFourCD_99310418264637080070954374437, phi_eightyFourCD_99310418264637080070954374438,
    phi_eightyFourCD_99310418264637080070954374439, phi_eightyFourCD_99310418264637080070954374440, phi_eightyFourCD_99310418264637080070954374441,
    phi_eightyFourCD_99310418264637080070954374442, phi_eightyFourCD_99310418264637080070954374443, phi_eightyFourCD_99310418264637080070954374444,
    phi_eightyFourCD_99310418264637080070954374445, phi_eightyFourCD_99310418264637080070954374446, phi_eightyFourCD_99310418264637080070954374447,
    phi_eightyFourCD_99310418264637080070954374448, phi_eightyFourCD_99310418264637080070954374449, phi_eightyFourCD_99310418264637080070954374450,
    phi_eightyFourCD_99310418264637080070954374451, phi_eightyFourCD_99310418264637080070954374452, phi_eightyFourCD_99310418264637080070954374453,
    phi_eightyFourCD_99310418264637080070954374454, phi_eightyFourCD_99310418264637080070954374455, phi_eightyFourCD_99310418264637080070954374456,
    phi_eightyFourCD_99310418264637080070954374457, phi_eightyFourCD_99310418264637080070954374458, phi_eightyFourCD_99310418264637080070954374459,
    phi_eightyFourCD_99310418264637080070954374460, phi_eightyFourCD_99310418264637080070954374461, phi_eightyFourCD_99310418264637080070954374462,
    phi_eightyFourCD_99310418264637080070954374463, phi_eightyFourCD_99310418264637080070954374464, phi_eightyFourCD_99310418264637080070954374465,
    phi_eightyFourCD_99310418264637080070954374466, phi_eightyFourCD_99310418264637080070954374467, phi_eightyFourCD_99310418264637080070954374468,
    phi_eightyFourCD_99310418264637080070954374469, phi_eightyFourCD_99310418264637080070954374470, phi_eightyFourCD_99310418264637080070954374471,
    phi_eightyFourCD_99310418264637080070954374472, phi_eightyFourCD_99310418264637080070954374473, phi_eightyFourCD_99310418264637080070954374474,
    phi_eightyFourCD_99310418264637080070954374475, phi_eightyFourCD_99310418264637080070954374476, phi_eightyFourCD_99310418264637080070954374477,
    phi_eightyFourCD_99310418264637080070954374478, phi_eightyFourCD_99310418264637080070954374479, phi_eightyFourCD_99310418264637080070954374480,
    phi_eightyFourCD_99310418264637080070954374481, phi_eightyFourCD_99310418264637080070954374482, phi_eightyFourCD_99310418264637080070954374483,
    phi_eightyFourCD_99310418264637080070954374484, phi_eightyFourCD_99310418264637080070954374485, phi_eightyFourCD_99310418264637080070954374486,
    phi_eightyFourCD_99310418264637080070954374487, phi_eightyFourCD_99310418264637080070954374488, phi_eightyFourCD_99310418264637080070954374489,
    phi_eightyFourCD_99310418264637080070954374490, phi_eightyFourCD_99310418264637080070954374491, phi_eightyFourCD_99310418264637080070954374492,
    phi_eightyFourCD_99310418264637080070954374493, phi_eightyFourCD_99310418264637080070954374494, phi_eightyFourCD_99310418264637080070954374495,
    phi_eightyFourCD_99310418264637080070954374496, phi_eightyFourCD_99310418264637080070954374497, phi_eightyFourCD_99310418264637080070954374498,
    phi_eightyFourCD_99310418264637080070954374499, phi_eightyFourCD_99310418264637080070954374500, phi_eightyFourCD_99310418264637080070954374501]

end TotientTailPeriodKiller
end Erdos249257
