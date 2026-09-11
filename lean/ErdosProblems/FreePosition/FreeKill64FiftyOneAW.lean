import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fiftyOneAWFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fiftyOneAWFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fiftyOneAWFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fiftyOneAWFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fiftyOneAWFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fiftyOneAWFastPow a n * fiftyOneAWFastPow a n * a
        else fiftyOneAWFastPow a n * fiftyOneAWFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fiftyOneAW_2 : Nat.Prime 2 := by norm_num
private theorem prime_fiftyOneAW_3 : Nat.Prime 3 := by norm_num
private theorem prime_fiftyOneAW_5 : Nat.Prime 5 := by norm_num
private theorem prime_fiftyOneAW_7 : Nat.Prime 7 := by norm_num
private theorem prime_fiftyOneAW_11 : Nat.Prime 11 := by norm_num
private theorem prime_fiftyOneAW_13 : Nat.Prime 13 := by norm_num
private theorem prime_fiftyOneAW_17 : Nat.Prime 17 := by norm_num
private theorem prime_fiftyOneAW_19 : Nat.Prime 19 := by norm_num
private theorem prime_fiftyOneAW_23 : Nat.Prime 23 := by norm_num
private theorem prime_fiftyOneAW_29 : Nat.Prime 29 := by norm_num
private theorem prime_fiftyOneAW_31 : Nat.Prime 31 := by norm_num
private theorem prime_fiftyOneAW_37 : Nat.Prime 37 := by norm_num
private theorem prime_fiftyOneAW_41 : Nat.Prime 41 := by norm_num
private theorem prime_fiftyOneAW_43 : Nat.Prime 43 := by norm_num
private theorem prime_fiftyOneAW_47 : Nat.Prime 47 := by norm_num
private theorem prime_fiftyOneAW_53 : Nat.Prime 53 := by norm_num
private theorem prime_fiftyOneAW_59 : Nat.Prime 59 := by norm_num
private theorem prime_fiftyOneAW_61 : Nat.Prime 61 := by norm_num
private theorem prime_fiftyOneAW_67 : Nat.Prime 67 := by norm_num
private theorem prime_fiftyOneAW_71 : Nat.Prime 71 := by norm_num
private theorem prime_fiftyOneAW_73 : Nat.Prime 73 := by norm_num
private theorem prime_fiftyOneAW_79 : Nat.Prime 79 := by norm_num
private theorem prime_fiftyOneAW_83 : Nat.Prime 83 := by norm_num
private theorem prime_fiftyOneAW_89 : Nat.Prime 89 := by norm_num
private theorem prime_fiftyOneAW_97 : Nat.Prime 97 := by norm_num
private theorem prime_fiftyOneAW_101 : Nat.Prime 101 := by norm_num
private theorem prime_fiftyOneAW_103 : Nat.Prime 103 := by norm_num
private theorem prime_fiftyOneAW_107 : Nat.Prime 107 := by norm_num
private theorem prime_fiftyOneAW_109 : Nat.Prime 109 := by norm_num
private theorem prime_fiftyOneAW_113 : Nat.Prime 113 := by norm_num
private theorem prime_fiftyOneAW_127 : Nat.Prime 127 := by norm_num
private theorem prime_fiftyOneAW_131 : Nat.Prime 131 := by norm_num
private theorem prime_fiftyOneAW_137 : Nat.Prime 137 := by norm_num
private theorem prime_fiftyOneAW_149 : Nat.Prime 149 := by norm_num
private theorem prime_fiftyOneAW_151 : Nat.Prime 151 := by norm_num
private theorem prime_fiftyOneAW_157 : Nat.Prime 157 := by norm_num
private theorem prime_fiftyOneAW_163 : Nat.Prime 163 := by norm_num
private theorem prime_fiftyOneAW_167 : Nat.Prime 167 := by norm_num
private theorem prime_fiftyOneAW_173 : Nat.Prime 173 := by norm_num
private theorem prime_fiftyOneAW_179 : Nat.Prime 179 := by norm_num
private theorem prime_fiftyOneAW_181 : Nat.Prime 181 := by norm_num
private theorem prime_fiftyOneAW_191 : Nat.Prime 191 := by norm_num
private theorem prime_fiftyOneAW_197 : Nat.Prime 197 := by norm_num
private theorem prime_fiftyOneAW_199 : Nat.Prime 199 := by norm_num
private theorem prime_fiftyOneAW_211 : Nat.Prime 211 := by norm_num
private theorem prime_fiftyOneAW_223 : Nat.Prime 223 := by norm_num
private theorem prime_fiftyOneAW_227 : Nat.Prime 227 := by norm_num
private theorem prime_fiftyOneAW_229 : Nat.Prime 229 := by norm_num
private theorem prime_fiftyOneAW_233 : Nat.Prime 233 := by norm_num
private theorem prime_fiftyOneAW_239 : Nat.Prime 239 := by norm_num
private theorem prime_fiftyOneAW_241 : Nat.Prime 241 := by norm_num
private theorem prime_fiftyOneAW_251 : Nat.Prime 251 := by norm_num
private theorem prime_fiftyOneAW_257 : Nat.Prime 257 := by norm_num
private theorem prime_fiftyOneAW_263 : Nat.Prime 263 := by norm_num
private theorem prime_fiftyOneAW_271 : Nat.Prime 271 := by norm_num
private theorem prime_fiftyOneAW_277 : Nat.Prime 277 := by norm_num
private theorem prime_fiftyOneAW_281 : Nat.Prime 281 := by norm_num
private theorem prime_fiftyOneAW_283 : Nat.Prime 283 := by norm_num
private theorem prime_fiftyOneAW_307 : Nat.Prime 307 := by norm_num
private theorem prime_fiftyOneAW_317 : Nat.Prime 317 := by norm_num
private theorem prime_fiftyOneAW_337 : Nat.Prime 337 := by norm_num
private theorem prime_fiftyOneAW_347 : Nat.Prime 347 := by norm_num
private theorem prime_fiftyOneAW_353 : Nat.Prime 353 := by norm_num
private theorem prime_fiftyOneAW_359 : Nat.Prime 359 := by norm_num
private theorem prime_fiftyOneAW_367 : Nat.Prime 367 := by norm_num
private theorem prime_fiftyOneAW_383 : Nat.Prime 383 := by norm_num
private theorem prime_fiftyOneAW_397 : Nat.Prime 397 := by norm_num
private theorem prime_fiftyOneAW_401 : Nat.Prime 401 := by norm_num
private theorem prime_fiftyOneAW_419 : Nat.Prime 419 := by norm_num
private theorem prime_fiftyOneAW_439 : Nat.Prime 439 := by norm_num
private theorem prime_fiftyOneAW_461 : Nat.Prime 461 := by norm_num
private theorem prime_fiftyOneAW_467 : Nat.Prime 467 := by norm_num
private theorem prime_fiftyOneAW_479 : Nat.Prime 479 := by norm_num
private theorem prime_fiftyOneAW_487 : Nat.Prime 487 := by norm_num
private theorem prime_fiftyOneAW_503 : Nat.Prime 503 := by norm_num
private theorem prime_fiftyOneAW_521 : Nat.Prime 521 := by norm_num
private theorem prime_fiftyOneAW_523 : Nat.Prime 523 := by norm_num
private theorem prime_fiftyOneAW_541 : Nat.Prime 541 := by norm_num
private theorem prime_fiftyOneAW_557 : Nat.Prime 557 := by norm_num
private theorem prime_fiftyOneAW_569 : Nat.Prime 569 := by norm_num
private theorem prime_fiftyOneAW_599 : Nat.Prime 599 := by norm_num
private theorem prime_fiftyOneAW_619 : Nat.Prime 619 := by norm_num
private theorem prime_fiftyOneAW_643 : Nat.Prime 643 := by norm_num
private theorem prime_fiftyOneAW_647 : Nat.Prime 647 := by norm_num
private theorem prime_fiftyOneAW_677 : Nat.Prime 677 := by norm_num
private theorem prime_fiftyOneAW_683 : Nat.Prime 683 := by norm_num
private theorem prime_fiftyOneAW_691 : Nat.Prime 691 := by norm_num
private theorem prime_fiftyOneAW_727 : Nat.Prime 727 := by norm_num
private theorem prime_fiftyOneAW_739 : Nat.Prime 739 := by norm_num
private theorem prime_fiftyOneAW_743 : Nat.Prime 743 := by norm_num
private theorem prime_fiftyOneAW_761 : Nat.Prime 761 := by norm_num
private theorem prime_fiftyOneAW_769 : Nat.Prime 769 := by norm_num
private theorem prime_fiftyOneAW_773 : Nat.Prime 773 := by norm_num
private theorem prime_fiftyOneAW_797 : Nat.Prime 797 := by norm_num
private theorem prime_fiftyOneAW_823 : Nat.Prime 823 := by norm_num
private theorem prime_fiftyOneAW_853 : Nat.Prime 853 := by norm_num
private theorem prime_fiftyOneAW_857 : Nat.Prime 857 := by norm_num
private theorem prime_fiftyOneAW_859 : Nat.Prime 859 := by norm_num
private theorem prime_fiftyOneAW_881 : Nat.Prime 881 := by norm_num
private theorem prime_fiftyOneAW_883 : Nat.Prime 883 := by norm_num
private theorem prime_fiftyOneAW_887 : Nat.Prime 887 := by norm_num
private theorem prime_fiftyOneAW_937 : Nat.Prime 937 := by norm_num
private theorem prime_fiftyOneAW_967 : Nat.Prime 967 := by norm_num
private theorem prime_fiftyOneAW_971 : Nat.Prime 971 := by norm_num
private theorem prime_fiftyOneAW_977 : Nat.Prime 977 := by norm_num
private theorem prime_fiftyOneAW_983 : Nat.Prime 983 := by norm_num
private theorem prime_fiftyOneAW_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_fiftyOneAW_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_fiftyOneAW_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_fiftyOneAW_1039 : Nat.Prime 1039 := by norm_num
private theorem prime_fiftyOneAW_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_fiftyOneAW_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_fiftyOneAW_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_fiftyOneAW_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_fiftyOneAW_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_fiftyOneAW_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_fiftyOneAW_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_fiftyOneAW_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_fiftyOneAW_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_fiftyOneAW_1181 : Nat.Prime 1181 := by norm_num
private theorem prime_fiftyOneAW_1193 : Nat.Prime 1193 := by norm_num
private theorem prime_fiftyOneAW_1231 : Nat.Prime 1231 := by norm_num
private theorem prime_fiftyOneAW_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_fiftyOneAW_1291 : Nat.Prime 1291 := by norm_num
private theorem prime_fiftyOneAW_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_fiftyOneAW_1361 : Nat.Prime 1361 := by norm_num
private theorem prime_fiftyOneAW_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_fiftyOneAW_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_fiftyOneAW_1553 : Nat.Prime 1553 := by norm_num
private theorem prime_fiftyOneAW_1601 : Nat.Prime 1601 := by norm_num
private theorem prime_fiftyOneAW_1621 : Nat.Prime 1621 := by norm_num
private theorem prime_fiftyOneAW_1637 : Nat.Prime 1637 := by norm_num
private theorem prime_fiftyOneAW_1657 : Nat.Prime 1657 := by norm_num
private theorem prime_fiftyOneAW_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_fiftyOneAW_1753 : Nat.Prime 1753 := by norm_num
private theorem prime_fiftyOneAW_1871 : Nat.Prime 1871 := by norm_num
private theorem prime_fiftyOneAW_2029 : Nat.Prime 2029 := by norm_num
private theorem prime_fiftyOneAW_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_fiftyOneAW_2179 : Nat.Prime 2179 := by norm_num
private theorem prime_fiftyOneAW_2207 : Nat.Prime 2207 := by norm_num
private theorem prime_fiftyOneAW_2273 : Nat.Prime 2273 := by norm_num
private theorem prime_fiftyOneAW_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_fiftyOneAW_2339 : Nat.Prime 2339 := by norm_num
private theorem prime_fiftyOneAW_2341 : Nat.Prime 2341 := by norm_num
private theorem prime_fiftyOneAW_2347 : Nat.Prime 2347 := by norm_num
private theorem prime_fiftyOneAW_2357 : Nat.Prime 2357 := by norm_num
private theorem prime_fiftyOneAW_2371 : Nat.Prime 2371 := by norm_num
private theorem prime_fiftyOneAW_2377 : Nat.Prime 2377 := by norm_num
private theorem prime_fiftyOneAW_2381 : Nat.Prime 2381 := by norm_num
private theorem prime_fiftyOneAW_2383 : Nat.Prime 2383 := by norm_num
private theorem prime_fiftyOneAW_2399 : Nat.Prime 2399 := by norm_num
private theorem prime_fiftyOneAW_2617 : Nat.Prime 2617 := by norm_num
private theorem prime_fiftyOneAW_2621 : Nat.Prime 2621 := by norm_num
private theorem prime_fiftyOneAW_2693 : Nat.Prime 2693 := by norm_num
private theorem prime_fiftyOneAW_2857 : Nat.Prime 2857 := by norm_num
private theorem prime_fiftyOneAW_2861 : Nat.Prime 2861 := by norm_num
private theorem prime_fiftyOneAW_3083 : Nat.Prime 3083 := by norm_num
private theorem prime_fiftyOneAW_3187 : Nat.Prime 3187 := by norm_num
private theorem prime_fiftyOneAW_3217 : Nat.Prime 3217 := by norm_num
private theorem prime_fiftyOneAW_3323 : Nat.Prime 3323 := by norm_num
private theorem prime_fiftyOneAW_3331 : Nat.Prime 3331 := by norm_num
private theorem prime_fiftyOneAW_3517 : Nat.Prime 3517 := by norm_num
private theorem prime_fiftyOneAW_3559 : Nat.Prime 3559 := by norm_num
private theorem prime_fiftyOneAW_3623 : Nat.Prime 3623 := by norm_num
private theorem prime_fiftyOneAW_3637 : Nat.Prime 3637 := by norm_num
private theorem prime_fiftyOneAW_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_fiftyOneAW_3719 : Nat.Prime 3719 := by norm_num
private theorem prime_fiftyOneAW_3779 : Nat.Prime 3779 := by norm_num
private theorem prime_fiftyOneAW_3863 : Nat.Prime 3863 := by norm_num
private theorem prime_fiftyOneAW_3881 : Nat.Prime 3881 := by norm_num
private theorem prime_fiftyOneAW_4019 : Nat.Prime 4019 := by norm_num
private theorem prime_fiftyOneAW_4219 : Nat.Prime 4219 := by norm_num
private theorem prime_fiftyOneAW_4241 : Nat.Prime 4241 := by norm_num
private theorem prime_fiftyOneAW_4801 : Nat.Prime 4801 := by norm_num
private theorem prime_fiftyOneAW_4831 : Nat.Prime 4831 := by norm_num
private theorem prime_fiftyOneAW_4919 : Nat.Prime 4919 := by norm_num
private theorem prime_fiftyOneAW_4937 : Nat.Prime 4937 := by norm_num
private theorem prime_fiftyOneAW_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fiftyOneAW_5147 : Nat.Prime 5147 := by norm_num
private theorem prime_fiftyOneAW_5197 : Nat.Prime 5197 := by norm_num
private theorem prime_fiftyOneAW_5233 : Nat.Prime 5233 := by norm_num
private theorem prime_fiftyOneAW_5281 : Nat.Prime 5281 := by norm_num
private theorem prime_fiftyOneAW_5387 : Nat.Prime 5387 := by norm_num
private theorem prime_fiftyOneAW_5501 : Nat.Prime 5501 := by norm_num
private theorem prime_fiftyOneAW_5641 : Nat.Prime 5641 := by norm_num
private theorem prime_fiftyOneAW_5653 : Nat.Prime 5653 := by norm_num
private theorem prime_fiftyOneAW_5657 : Nat.Prime 5657 := by norm_num
private theorem prime_fiftyOneAW_5701 : Nat.Prime 5701 := by norm_num
private theorem prime_fiftyOneAW_5743 : Nat.Prime 5743 := by norm_num
private theorem prime_fiftyOneAW_6211 : Nat.Prime 6211 := by norm_num
private theorem prime_fiftyOneAW_6287 : Nat.Prime 6287 := by norm_num
private theorem prime_fiftyOneAW_6311 : Nat.Prime 6311 := by norm_num
private theorem prime_fiftyOneAW_6337 : Nat.Prime 6337 := by norm_num
private theorem prime_fiftyOneAW_6397 : Nat.Prime 6397 := by norm_num
private theorem prime_fiftyOneAW_6451 : Nat.Prime 6451 := by norm_num
private theorem prime_fiftyOneAW_6551 : Nat.Prime 6551 := by norm_num
private theorem prime_fiftyOneAW_6569 : Nat.Prime 6569 := by norm_num
private theorem prime_fiftyOneAW_6827 : Nat.Prime 6827 := by norm_num
private theorem prime_fiftyOneAW_6971 : Nat.Prime 6971 := by norm_num
private theorem prime_fiftyOneAW_7069 : Nat.Prime 7069 := by norm_num
private theorem prime_fiftyOneAW_7253 : Nat.Prime 7253 := by norm_num
private theorem prime_fiftyOneAW_7411 : Nat.Prime 7411 := by norm_num
private theorem prime_fiftyOneAW_7481 : Nat.Prime 7481 := by norm_num
private theorem prime_fiftyOneAW_7529 : Nat.Prime 7529 := by norm_num
private theorem prime_fiftyOneAW_7963 : Nat.Prime 7963 := by norm_num
private theorem prime_fiftyOneAW_8111 : Nat.Prime 8111 := by norm_num
private theorem prime_fiftyOneAW_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_fiftyOneAW_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_fiftyOneAW_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_fiftyOneAW_8893 : Nat.Prime 8893 := by norm_num
private theorem prime_fiftyOneAW_9013 : Nat.Prime 9013 := by norm_num
private theorem prime_fiftyOneAW_9283 : Nat.Prime 9283 := by norm_num
private theorem prime_fiftyOneAW_9497 : Nat.Prime 9497 := by norm_num
private theorem prime_fiftyOneAW_9547 : Nat.Prime 9547 := by norm_num
private theorem prime_fiftyOneAW_9803 : Nat.Prime 9803 := by norm_num
private theorem prime_fiftyOneAW_9829 : Nat.Prime 9829 := by norm_num
private theorem prime_fiftyOneAW_10267 : Nat.Prime 10267 := by norm_num
private theorem prime_fiftyOneAW_10691 : Nat.Prime 10691 := by norm_num
private theorem prime_fiftyOneAW_10883 : Nat.Prime 10883 := by norm_num
private theorem prime_fiftyOneAW_11213 : Nat.Prime 11213 := by norm_num
private theorem prime_fiftyOneAW_11317 : Nat.Prime 11317 := by norm_num
private theorem prime_fiftyOneAW_11833 : Nat.Prime 11833 := by norm_num
private theorem prime_fiftyOneAW_11941 : Nat.Prime 11941 := by norm_num
private theorem prime_fiftyOneAW_12227 : Nat.Prime 12227 := by norm_num
private theorem prime_fiftyOneAW_12373 : Nat.Prime 12373 := by norm_num
private theorem prime_fiftyOneAW_12973 : Nat.Prime 12973 := by norm_num
private theorem prime_fiftyOneAW_15583 : Nat.Prime 15583 := by norm_num
private theorem prime_fiftyOneAW_16603 : Nat.Prime 16603 := by norm_num
private theorem prime_fiftyOneAW_18059 : Nat.Prime 18059 := by norm_num
private theorem prime_fiftyOneAW_18133 : Nat.Prime 18133 := by norm_num
private theorem prime_fiftyOneAW_19421 : Nat.Prime 19421 := by norm_num
private theorem prime_fiftyOneAW_19891 : Nat.Prime 19891 := by norm_num
private theorem prime_fiftyOneAW_20509 : Nat.Prime 20509 := by norm_num
private theorem prime_fiftyOneAW_20947 : Nat.Prime 20947 := by norm_num
private theorem prime_fiftyOneAW_21881 : Nat.Prime 21881 := by norm_num
private theorem prime_fiftyOneAW_22409 : Nat.Prime 22409 := by norm_num
private theorem prime_fiftyOneAW_22441 : Nat.Prime 22441 := by norm_num
private theorem prime_fiftyOneAW_22571 : Nat.Prime 22571 := by norm_num
private theorem prime_fiftyOneAW_23549 : Nat.Prime 23549 := by norm_num
private theorem prime_fiftyOneAW_25127 : Nat.Prime 25127 := by norm_num
private theorem prime_fiftyOneAW_28547 : Nat.Prime 28547 := by norm_num
private theorem prime_fiftyOneAW_28859 : Nat.Prime 28859 := by norm_num
private theorem prime_fiftyOneAW_29641 : Nat.Prime 29641 := by norm_num
private theorem prime_fiftyOneAW_31319 : Nat.Prime 31319 := by norm_num
private theorem prime_fiftyOneAW_32359 : Nat.Prime 32359 := by norm_num
private theorem prime_fiftyOneAW_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_fiftyOneAW_36299 : Nat.Prime 36299 := by norm_num
private theorem prime_fiftyOneAW_37847 : Nat.Prime 37847 := by norm_num
private theorem prime_fiftyOneAW_40163 : Nat.Prime 40163 := by norm_num
private theorem prime_fiftyOneAW_42571 : Nat.Prime 42571 := by norm_num
private theorem prime_fiftyOneAW_44263 : Nat.Prime 44263 := by norm_num
private theorem prime_fiftyOneAW_45263 : Nat.Prime 45263 := by norm_num
private theorem prime_fiftyOneAW_46133 : Nat.Prime 46133 := by norm_num
private theorem prime_fiftyOneAW_49279 : Nat.Prime 49279 := by norm_num
private theorem prime_fiftyOneAW_49417 : Nat.Prime 49417 := by norm_num
private theorem prime_fiftyOneAW_54601 : Nat.Prime 54601 := by norm_num
private theorem prime_fiftyOneAW_54833 : Nat.Prime 54833 := by norm_num
private theorem prime_fiftyOneAW_55103 : Nat.Prime 55103 := by norm_num
private theorem prime_fiftyOneAW_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_fiftyOneAW_66751 : Nat.Prime 66751 := by norm_num
private theorem prime_fiftyOneAW_67411 : Nat.Prime 67411 := by norm_num
private theorem prime_fiftyOneAW_67901 : Nat.Prime 67901 := by norm_num
private theorem prime_fiftyOneAW_68947 : Nat.Prime 68947 := by norm_num
private theorem prime_fiftyOneAW_72869 : Nat.Prime 72869 := by norm_num
private theorem prime_fiftyOneAW_75133 : Nat.Prime 75133 := by norm_num
private theorem prime_fiftyOneAW_76679 : Nat.Prime 76679 := by norm_num
private theorem prime_fiftyOneAW_79579 : Nat.Prime 79579 := by norm_num
private theorem prime_fiftyOneAW_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_fiftyOneAW_83047 : Nat.Prime 83047 := by norm_num
private theorem prime_fiftyOneAW_84503 : Nat.Prime 84503 := by norm_num
private theorem prime_fiftyOneAW_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_fiftyOneAW_101839 : Nat.Prime 101839 := by norm_num
private theorem prime_fiftyOneAW_111187 : Nat.Prime 111187 := by norm_num
private theorem prime_fiftyOneAW_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_fiftyOneAW_120193 : Nat.Prime 120193 := by norm_num
private theorem prime_fiftyOneAW_136601 : Nat.Prime 136601 := by norm_num
private theorem prime_fiftyOneAW_141023 : Nat.Prime 141023 := by norm_num
private theorem prime_fiftyOneAW_157477 : Nat.Prime 157477 := by norm_num
private theorem prime_fiftyOneAW_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_fiftyOneAW_162917 : Nat.Prime 162917 := by norm_num
private theorem prime_fiftyOneAW_172307 : Nat.Prime 172307 := by norm_num
private theorem prime_fiftyOneAW_173293 : Nat.Prime 173293 := by norm_num
private theorem prime_fiftyOneAW_177493 : Nat.Prime 177493 := by norm_num
private theorem prime_fiftyOneAW_182887 : Nat.Prime 182887 := by norm_num
private theorem prime_fiftyOneAW_187477 : Nat.Prime 187477 := by norm_num
private theorem prime_fiftyOneAW_187751 : Nat.Prime 187751 := by norm_num
private theorem prime_fiftyOneAW_197969 : Nat.Prime 197969 := by norm_num
private theorem prime_fiftyOneAW_200297 : Nat.Prime 200297 := by norm_num
private theorem prime_fiftyOneAW_201491 : Nat.Prime 201491 := by norm_num
private theorem prime_fiftyOneAW_206489 : Nat.Prime 206489 := by norm_num
private theorem prime_fiftyOneAW_206641 : Nat.Prime 206641 := by norm_num
private theorem prime_fiftyOneAW_207941 : Nat.Prime 207941 := by norm_num
private theorem prime_fiftyOneAW_208333 : Nat.Prime 208333 := by norm_num
private theorem prime_fiftyOneAW_212081 : Nat.Prime 212081 := by norm_num
private theorem prime_fiftyOneAW_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_fiftyOneAW_223283 : Nat.Prime 223283 := by norm_num
private theorem prime_fiftyOneAW_251149 : Nat.Prime 251149 := by norm_num
private theorem prime_fiftyOneAW_299027 : Nat.Prime 299027 := by norm_num
private theorem prime_fiftyOneAW_299311 : Nat.Prime 299311 := by norm_num
private theorem prime_fiftyOneAW_312509 : Nat.Prime 312509 := by norm_num
private theorem prime_fiftyOneAW_327263 : Nat.Prime 327263 := by norm_num
private theorem prime_fiftyOneAW_341659 : Nat.Prime 341659 := by norm_num
private theorem prime_fiftyOneAW_347759 : Nat.Prime 347759 := by norm_num
private theorem prime_fiftyOneAW_352237 : Nat.Prime 352237 := by norm_num
private theorem prime_fiftyOneAW_375227 : Nat.Prime 375227 := by norm_num
private theorem prime_fiftyOneAW_391073 : Nat.Prime 391073 := by norm_num
private theorem prime_fiftyOneAW_401867 : Nat.Prime 401867 := by norm_num
private theorem prime_fiftyOneAW_411143 : Nat.Prime 411143 := by norm_num
private theorem prime_fiftyOneAW_425911 : Nat.Prime 425911 := by norm_num
private theorem prime_fiftyOneAW_439441 : Nat.Prime 439441 := by norm_num
private theorem prime_fiftyOneAW_442919 : Nat.Prime 442919 := by norm_num
private theorem prime_fiftyOneAW_458629 : Nat.Prime 458629 := by norm_num
private theorem prime_fiftyOneAW_477409 : Nat.Prime 477409 := by norm_num
private theorem prime_fiftyOneAW_572791 : Nat.Prime 572791 := by norm_num
private theorem prime_fiftyOneAW_572867 : Nat.Prime 572867 := by norm_num
private theorem prime_fiftyOneAW_588881 : Nat.Prime 588881 := by norm_num
private theorem prime_fiftyOneAW_617363 : Nat.Prime 617363 := by norm_num
private theorem prime_fiftyOneAW_627481 : Nat.Prime 627481 := by norm_num
private theorem prime_fiftyOneAW_648239 : Nat.Prime 648239 := by norm_num
private theorem prime_fiftyOneAW_659171 : Nat.Prime 659171 := by norm_num
private theorem prime_fiftyOneAW_680321 : Nat.Prime 680321 := by norm_num
private theorem prime_fiftyOneAW_718457 : Nat.Prime 718457 := by norm_num
private theorem prime_fiftyOneAW_799361 : Nat.Prime 799361 := by norm_num
private theorem prime_fiftyOneAW_851009 : Nat.Prime 851009 := by norm_num
private theorem prime_fiftyOneAW_865643 : Nat.Prime 865643 := by norm_num
private theorem prime_fiftyOneAW_878719 : Nat.Prime 878719 := by norm_num
private theorem prime_fiftyOneAW_958877 : Nat.Prime 958877 := by norm_num
private theorem prime_fiftyOneAW_1034861 : Nat.Prime 1034861 := by norm_num
private theorem prime_fiftyOneAW_1076753 : Nat.Prime 1076753 := by norm_num
private theorem prime_fiftyOneAW_1101641 : Nat.Prime 1101641 := by norm_num
private theorem prime_fiftyOneAW_1133689 : Nat.Prime 1133689 := by norm_num
private theorem prime_fiftyOneAW_1167833 : Nat.Prime 1167833 := by norm_num
private theorem prime_fiftyOneAW_1168799 : Nat.Prime 1168799 := by norm_num
private theorem prime_fiftyOneAW_1231261 : Nat.Prime 1231261 := by norm_num
private theorem prime_fiftyOneAW_1301957 : Nat.Prime 1301957 := by norm_num
private theorem prime_fiftyOneAW_1417541 : Nat.Prime 1417541 := by norm_num
private theorem prime_fiftyOneAW_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_fiftyOneAW_1578091 : Nat.Prime 1578091 := by norm_num
private theorem prime_fiftyOneAW_1610527 : Nat.Prime 1610527 := by norm_num
private theorem prime_fiftyOneAW_1646189 : Nat.Prime 1646189 := by norm_num
private theorem prime_fiftyOneAW_1743067 : Nat.Prime 1743067 := by norm_num
private theorem prime_fiftyOneAW_1850837 : Nat.Prime 1850837 := by norm_num
private theorem prime_fiftyOneAW_2241583 : Nat.Prime 2241583 := by norm_num
private theorem prime_fiftyOneAW_2413679 : Nat.Prime 2413679 := by norm_num
private theorem prime_fiftyOneAW_2432869 : Nat.Prime 2432869 := by norm_num
private theorem prime_fiftyOneAW_2584079 : Nat.Prime 2584079 := by norm_num
private theorem prime_fiftyOneAW_2705069 : Nat.Prime 2705069 := by norm_num
private theorem prime_fiftyOneAW_2993093 : Nat.Prime 2993093 := by norm_num
private theorem prime_fiftyOneAW_3013783 : Nat.Prime 3013783 := by norm_num
private theorem prime_fiftyOneAW_3033883 : Nat.Prime 3033883 := by norm_num
private theorem prime_fiftyOneAW_3395999 : Nat.Prime 3395999 := by norm_num
private theorem prime_fiftyOneAW_3427181 : Nat.Prime 3427181 := by norm_num
private theorem prime_fiftyOneAW_3436841 : Nat.Prime 3436841 := by norm_num
private theorem prime_fiftyOneAW_3606989 : Nat.Prime 3606989 := by norm_num
private theorem prime_fiftyOneAW_3960137 : Nat.Prime 3960137 := by norm_num
private theorem prime_fiftyOneAW_4321049 : Nat.Prime 4321049 := by norm_num
private theorem prime_fiftyOneAW_4523579 : Nat.Prime 4523579 := by norm_num
private theorem prime_fiftyOneAW_4915219 : Nat.Prime 4915219 := by norm_num
private theorem prime_fiftyOneAW_4930417 : Nat.Prime 4930417 := by norm_num
private theorem prime_fiftyOneAW_5371403 : Nat.Prime 5371403 := by norm_num
private theorem prime_fiftyOneAW_5475539 : Nat.Prime 5475539 := by norm_num
private theorem prime_fiftyOneAW_5570909 : Nat.Prime 5570909 := by norm_num
private theorem prime_fiftyOneAW_6090257 : Nat.Prime 6090257 := by norm_num
private theorem prime_fiftyOneAW_6446633 : Nat.Prime 6446633 := by norm_num
private theorem prime_fiftyOneAW_6889997 : Nat.Prime 6889997 := by norm_num
private theorem prime_fiftyOneAW_7049113 : Nat.Prime 7049113 := by norm_num
private theorem prime_fiftyOneAW_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_fiftyOneAW_7197349 : Nat.Prime 7197349 := by norm_num
private theorem prime_fiftyOneAW_7303909 : Nat.Prime 7303909 := by norm_num
private theorem prime_fiftyOneAW_7367011 : Nat.Prime 7367011 := by norm_num
private theorem prime_fiftyOneAW_7456769 : Nat.Prime 7456769 := by norm_num
private theorem prime_fiftyOneAW_7661581 : Nat.Prime 7661581 := by norm_num
private theorem prime_fiftyOneAW_7815337 : Nat.Prime 7815337 := by norm_num
private theorem prime_fiftyOneAW_7906163 : Nat.Prime 7906163 := by norm_num
private theorem prime_fiftyOneAW_7919287 : Nat.Prime 7919287 := by norm_num
private theorem prime_fiftyOneAW_8134051 : Nat.Prime 8134051 := by norm_num
private theorem prime_fiftyOneAW_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_fiftyOneAW_8392481 : Nat.Prime 8392481 := by norm_num
private theorem prime_fiftyOneAW_8451647 : Nat.Prime 8451647 := by norm_num
private theorem prime_fiftyOneAW_8511353 : Nat.Prime 8511353 := by norm_num
private theorem prime_fiftyOneAW_8574737 : Nat.Prime 8574737 := by norm_num
private theorem prime_fiftyOneAW_8767271 : Nat.Prime 8767271 := by norm_num
private theorem prime_fiftyOneAW_8886667 : Nat.Prime 8886667 := by norm_num
private theorem prime_fiftyOneAW_9792301 : Nat.Prime 9792301 := by norm_num
private theorem prime_fiftyOneAW_9910249 : Nat.Prime 9910249 := by norm_num
private theorem prime_fiftyOneAW_9978323 : Nat.Prime 9978323 := by norm_num
private theorem prime_fiftyOneAW_10136207 : Nat.Prime 10136207 := by norm_num
private theorem prime_fiftyOneAW_10618457 : Nat.Prime 10618457 := by norm_num
private theorem prime_fiftyOneAW_11452853 : Nat.Prime 11452853 := by norm_num
private theorem prime_fiftyOneAW_11713441 : Nat.Prime 11713441 := by norm_num
private theorem prime_fiftyOneAW_12442349 : Nat.Prime 12442349 := by norm_num
private theorem prime_fiftyOneAW_12773071 : Nat.Prime 12773071 := by norm_num
private theorem prime_fiftyOneAW_13251499 : Nat.Prime 13251499 := by norm_num
private theorem prime_fiftyOneAW_13517267 : Nat.Prime 13517267 := by norm_num
private theorem prime_fiftyOneAW_13974019 : Nat.Prime 13974019 := by norm_num
private theorem prime_fiftyOneAW_14196001 : Nat.Prime 14196001 := by norm_num
private theorem prime_fiftyOneAW_14708171 : Nat.Prime 14708171 := by norm_num
private theorem prime_fiftyOneAW_14788387 : Nat.Prime 14788387 := by norm_num
private theorem prime_fiftyOneAW_14999741 : Nat.Prime 14999741 := by norm_num
private theorem prime_fiftyOneAW_16046729 : Nat.Prime 16046729 := by norm_num
private theorem prime_fiftyOneAW_17958571 : Nat.Prime 17958571 := by norm_num
private theorem prime_fiftyOneAW_18225469 : Nat.Prime 18225469 := by norm_num
private theorem prime_fiftyOneAW_18739561 : Nat.Prime 18739561 := by norm_num
private theorem prime_fiftyOneAW_21354913 : Nat.Prime 21354913 := by norm_num
private theorem prime_fiftyOneAW_21642461 : Nat.Prime 21642461 := by norm_num
private theorem prime_fiftyOneAW_23696867 : Nat.Prime 23696867 := by norm_num
private theorem prime_fiftyOneAW_24357611 : Nat.Prime 24357611 := by norm_num
private theorem prime_fiftyOneAW_25279049 : Nat.Prime 25279049 := by norm_num
private theorem prime_fiftyOneAW_25969733 : Nat.Prime 25969733 := by norm_num
private theorem prime_fiftyOneAW_28094537 : Nat.Prime 28094537 := by norm_num
private theorem prime_fiftyOneAW_28130321 : Nat.Prime 28130321 := by norm_num

private theorem prime_fiftyOneAW_31346449 : Nat.Prime 31346449 := by
  apply lucas_primality 31346449 (11 : ZMod 31346449)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (29, 1), (3217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (29, 1), (3217, 1)] : List FactorBlock).map factorBlockValue).prod) = 31346449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_3217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 31346449) ^ 15673224 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 31346449) ^ 10448816 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 31346449) ^ 4478064 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 31346449) ^ 1080912 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 31346449) ^ 9744 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_37952209 : Nat.Prime 37952209 := by
  apply lucas_primality 37952209 (19 : ZMod 37952209)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (23, 1), (1637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (23, 1), (1637, 1)] : List FactorBlock).map factorBlockValue).prod) = 37952209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_1637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 37952209) ^ 18976104 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 37952209) ^ 12650736 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 37952209) ^ 5421744 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 37952209) ^ 1650096 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 37952209) ^ 23184 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_38264113 : Nat.Prime 38264113 := by
  apply lucas_primality 38264113 (7 : ZMod 38264113)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (467, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (467, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) = 38264113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_467
      · exact prime_fiftyOneAW_569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 38264113) ^ 19132056 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 38264113) ^ 12754704 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 38264113) ^ 81936 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 38264113) ^ 67248 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_39125003 : Nat.Prime 39125003 := by
  apply lucas_primality 39125003 (2 : ZMod 39125003)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 2), (3323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 2), (3323, 1)] : List FactorBlock).map factorBlockValue).prod) = 39125003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_3323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39125003) ^ 19562501 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 39125003) ^ 5589286 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 39125003) ^ 1349138 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 39125003) ^ 11774 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_41833609 : Nat.Prime 41833609 := by
  apply lucas_primality 41833609 (41 : ZMod 41833609)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1743067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1743067, 1)] : List FactorBlock).map factorBlockValue).prod) = 41833609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_1743067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (41 : ZMod 41833609) ^ 20916804 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (41 : ZMod 41833609) ^ 13944536 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (41 : ZMod 41833609) ^ 24 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_42857783 : Nat.Prime 42857783 := by
  apply lucas_primality 42857783 (5 : ZMod 42857783)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod) = 42857783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42857783) ^ 21428891 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 3896162 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 2521046 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 374 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_44567273 : Nat.Prime 44567273 := by
  apply lucas_primality 44567273 (3 : ZMod 44567273)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5570909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5570909, 1)] : List FactorBlock).map factorBlockValue).prod) = 44567273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5570909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 44567273) ^ 22283636 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 44567273) ^ 8 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_47715119 : Nat.Prime 47715119 := by
  apply lucas_primality 47715119 (7 : ZMod 47715119)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (211, 1), (541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (211, 1), (541, 1)] : List FactorBlock).map factorBlockValue).prod) = 47715119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_211
      · exact prime_fiftyOneAW_541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 47715119) ^ 23857559 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 47715119) ^ 4337738 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 47715119) ^ 2511322 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 47715119) ^ 226138 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 47715119) ^ 88198 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_51939467 : Nat.Prime 51939467 := by
  apply lucas_primality 51939467 (2 : ZMod 51939467)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25969733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25969733, 1)] : List FactorBlock).map factorBlockValue).prod) = 51939467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_25969733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 51939467) ^ 25969733 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 51939467) ^ 2 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_52142977 : Nat.Prime 52142977 := by
  apply lucas_primality 52142977 (5 : ZMod 52142977)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (45263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (45263, 1)] : List FactorBlock).map factorBlockValue).prod) = 52142977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_45263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 52142977) ^ 26071488 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 52142977) ^ 17380992 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 52142977) ^ 1152 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_59941267 : Nat.Prime 59941267 := by
  apply lucas_primality 59941267 (7 : ZMod 59941267)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (23, 1), (5641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (23, 1), (5641, 1)] : List FactorBlock).map factorBlockValue).prod) = 59941267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_5641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 59941267) ^ 29970633 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 59941267) ^ 19980422 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 59941267) ^ 8563038 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 59941267) ^ 5449206 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 59941267) ^ 2606142 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 59941267) ^ 10626 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_60817243 : Nat.Prime 60817243 := by
  apply lucas_primality 60817243 (2 : ZMod 60817243)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (10136207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (10136207, 1)] : List FactorBlock).map factorBlockValue).prod) = 60817243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_10136207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 60817243) ^ 30408621 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 60817243) ^ 20272414 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 60817243) ^ 6 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_60959293 : Nat.Prime 60959293 := by
  apply lucas_primality 60959293 (2 : ZMod 60959293)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (41, 1), (5387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (41, 1), (5387, 1)] : List FactorBlock).map factorBlockValue).prod) = 60959293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_41
      · exact prime_fiftyOneAW_5387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60959293) ^ 30479646 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 60959293) ^ 20319764 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 60959293) ^ 2650404 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 60959293) ^ 1486812 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 60959293) ^ 11316 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_61906253 : Nat.Prime 61906253 := by
  apply lucas_primality 61906253 (2 : ZMod 61906253)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (857, 1), (18059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (857, 1), (18059, 1)] : List FactorBlock).map factorBlockValue).prod) = 61906253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_857
      · exact prime_fiftyOneAW_18059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 61906253) ^ 30953126 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 61906253) ^ 72236 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 61906253) ^ 3428 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_62602601 : Nat.Prime 62602601 := by
  apply lucas_primality 62602601 (3 : ZMod 62602601)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (89, 1), (3517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (89, 1), (3517, 1)] : List FactorBlock).map factorBlockValue).prod) = 62602601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_89
      · exact prime_fiftyOneAW_3517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 62602601) ^ 31301300 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 62602601) ^ 12520520 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 62602601) ^ 703400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 62602601) ^ 17800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_70633193 : Nat.Prime 70633193 := by
  apply lucas_primality 70633193 (3 : ZMod 70633193)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (977, 1), (1291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (977, 1), (1291, 1)] : List FactorBlock).map factorBlockValue).prod) = 70633193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_977
      · exact prime_fiftyOneAW_1291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 70633193) ^ 35316596 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 70633193) ^ 10090456 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 70633193) ^ 72296 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 70633193) ^ 54712 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_73627703 : Nat.Prime 73627703 := by
  apply lucas_primality 73627703 (5 : ZMod 73627703)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5281, 1), (6971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5281, 1), (6971, 1)] : List FactorBlock).map factorBlockValue).prod) = 73627703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5281
      · exact prime_fiftyOneAW_6971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 73627703) ^ 36813851 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 73627703) ^ 13942 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 73627703) ^ 10562 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_79192871 : Nat.Prime 79192871 := by
  apply lucas_primality 79192871 (14 : ZMod 79192871)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7919287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7919287, 1)] : List FactorBlock).map factorBlockValue).prod) = 79192871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7919287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 79192871) ^ 39596435 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (14 : ZMod 79192871) ^ 15838574 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (14 : ZMod 79192871) ^ 10 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_84294913 : Nat.Prime 84294913 := by
  apply lucas_primality 84294913 (14 : ZMod 84294913)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) = 84294913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 84294913) ^ 42147456 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 28098304 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 6484224 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 9984 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_88685873 : Nat.Prime 88685873 := by
  apply lucas_primality 88685873 (3 : ZMod 88685873)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (17, 1), (29641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (17, 1), (29641, 1)] : List FactorBlock).map factorBlockValue).prod) = 88685873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_29641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 88685873) ^ 44342936 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 88685873) ^ 8062352 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 88685873) ^ 5216816 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 88685873) ^ 2992 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_89134547 : Nat.Prime 89134547 := by
  apply lucas_primality 89134547 (2 : ZMod 89134547)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (44567273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (44567273, 1)] : List FactorBlock).map factorBlockValue).prod) = 89134547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_44567273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 89134547) ^ 44567273 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 89134547) ^ 2 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_89981557 : Nat.Prime 89981557 := by
  apply lucas_primality 89981557 (5 : ZMod 89981557)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1031, 1), (1039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1031, 1), (1039, 1)] : List FactorBlock).map factorBlockValue).prod) = 89981557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_1031
      · exact prime_fiftyOneAW_1039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 89981557) ^ 44990778 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 89981557) ^ 29993852 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 89981557) ^ 12854508 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 89981557) ^ 87276 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 89981557) ^ 86604 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_95430239 : Nat.Prime 95430239 := by
  apply lucas_primality 95430239 (7 : ZMod 95430239)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47715119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47715119, 1)] : List FactorBlock).map factorBlockValue).prod) = 95430239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_47715119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 95430239) ^ 47715119 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 95430239) ^ 2 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_101815639 : Nat.Prime 101815639 := by
  apply lucas_primality 101815639 (6 : ZMod 101815639)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (458629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (458629, 1)] : List FactorBlock).map factorBlockValue).prod) = 101815639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_37
      · exact prime_fiftyOneAW_458629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 101815639) ^ 50907819 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 101815639) ^ 33938546 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 101815639) ^ 2751774 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 101815639) ^ 222 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_105207253 : Nat.Prime 105207253 := by
  apply lucas_primality 105207253 (2 : ZMod 105207253)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8767271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8767271, 1)] : List FactorBlock).map factorBlockValue).prod) = 105207253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_8767271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 105207253) ^ 52603626 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 105207253) ^ 35069084 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 105207253) ^ 12 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_109178521 : Nat.Prime 109178521 := by
  apply lucas_primality 109178521 (23 : ZMod 109178521)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (107, 1), (773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (107, 1), (773, 1)] : List FactorBlock).map factorBlockValue).prod) = 109178521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_107
      · exact prime_fiftyOneAW_773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 109178521) ^ 54589260 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (23 : ZMod 109178521) ^ 36392840 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (23 : ZMod 109178521) ^ 21835704 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (23 : ZMod 109178521) ^ 9925320 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (23 : ZMod 109178521) ^ 1020360 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (23 : ZMod 109178521) ^ 141240 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_111306893 : Nat.Prime 111306893 := by
  apply lucas_primality 111306893 (2 : ZMod 111306893)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (352237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (352237, 1)] : List FactorBlock).map factorBlockValue).prod) = 111306893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_79
      · exact prime_fiftyOneAW_352237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 111306893) ^ 55653446 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 111306893) ^ 1408948 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 111306893) ^ 316 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_111386221 : Nat.Prime 111386221 := by
  apply lucas_primality 111386221 (2 : ZMod 111386221)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (71, 1), (2377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (71, 1), (2377, 1)] : List FactorBlock).map factorBlockValue).prod) = 111386221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_71
      · exact prime_fiftyOneAW_2377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 111386221) ^ 55693110 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 111386221) ^ 37128740 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 111386221) ^ 22277244 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 111386221) ^ 10126020 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 111386221) ^ 1568820 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 111386221) ^ 46860 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_113520457 : Nat.Prime 113520457 := by
  apply lucas_primality 113520457 (5 : ZMod 113520457)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 2), (23, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 2), (23, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) = 113520457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_1399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 113520457) ^ 56760228 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 113520457) ^ 37840152 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 113520457) ^ 16217208 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 113520457) ^ 4935672 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 113520457) ^ 81144 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_117665369 : Nat.Prime 117665369 := by
  apply lucas_primality 117665369 (3 : ZMod 117665369)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (14708171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (14708171, 1)] : List FactorBlock).map factorBlockValue).prod) = 117665369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_14708171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 117665369) ^ 58832684 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 117665369) ^ 8 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_117872177 : Nat.Prime 117872177 := by
  apply lucas_primality 117872177 (3 : ZMod 117872177)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7367011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7367011, 1)] : List FactorBlock).map factorBlockValue).prod) = 117872177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_7367011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 117872177) ^ 58936088 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 117872177) ^ 16 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_122594851 : Nat.Prime 122594851 := by
  apply lucas_primality 122594851 (2 : ZMod 122594851)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (7, 1), (12973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (7, 1), (12973, 1)] : List FactorBlock).map factorBlockValue).prod) = 122594851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_12973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 122594851) ^ 61297425 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 122594851) ^ 40864950 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 122594851) ^ 24518970 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 122594851) ^ 17513550 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 122594851) ^ 9450 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_123846461 : Nat.Prime 123846461 := by
  apply lucas_primality 123846461 (2 : ZMod 123846461)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (283, 1), (21881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (283, 1), (21881, 1)] : List FactorBlock).map factorBlockValue).prod) = 123846461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_283
      · exact prime_fiftyOneAW_21881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 123846461) ^ 61923230 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 123846461) ^ 24769292 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 123846461) ^ 437620 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 123846461) ^ 5660 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_133416637 : Nat.Prime 133416637 := by
  apply lucas_primality 133416637 (6 : ZMod 133416637)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (241, 1), (46133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (241, 1), (46133, 1)] : List FactorBlock).map factorBlockValue).prod) = 133416637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_241
      · exact prime_fiftyOneAW_46133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 133416637) ^ 66708318 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 133416637) ^ 44472212 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 133416637) ^ 553596 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 133416637) ^ 2892 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_140925283 : Nat.Prime 140925283 := by
  apply lucas_primality 140925283 (3 : ZMod 140925283)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (572867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (572867, 1)] : List FactorBlock).map factorBlockValue).prod) = 140925283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_41
      · exact prime_fiftyOneAW_572867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 140925283) ^ 70462641 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 140925283) ^ 46975094 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 140925283) ^ 3437202 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 140925283) ^ 246 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_144295631 : Nat.Prime 144295631 := by
  apply lucas_primality 144295631 (7 : ZMod 144295631)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (643, 1), (22441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (643, 1), (22441, 1)] : List FactorBlock).map factorBlockValue).prod) = 144295631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_643
      · exact prime_fiftyOneAW_22441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 144295631) ^ 72147815 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 144295631) ^ 28859126 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 144295631) ^ 224410 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 144295631) ^ 6430 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_155976109 : Nat.Prime 155976109 := by
  apply lucas_primality 155976109 (2 : ZMod 155976109)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (173, 1), (75133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (173, 1), (75133, 1)] : List FactorBlock).map factorBlockValue).prod) = 155976109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_173
      · exact prime_fiftyOneAW_75133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 155976109) ^ 77988054 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 155976109) ^ 51992036 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 155976109) ^ 901596 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 155976109) ^ 2076 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_167422603 : Nat.Prime 167422603 := by
  apply lucas_primality 167422603 (3 : ZMod 167422603)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (157, 1), (223, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (157, 1), (223, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod) = 167422603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_157
      · exact prime_fiftyOneAW_223
      · exact prime_fiftyOneAW_797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 167422603) ^ 83711301 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 167422603) ^ 55807534 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 167422603) ^ 1066386 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 167422603) ^ 750774 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 167422603) ^ 210066 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_234899479 : Nat.Prime 234899479 := by
  apply lucas_primality 234899479 (6 : ZMod 234899479)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 2), (29, 1), (3719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 2), (29, 1), (3719, 1)] : List FactorBlock).map factorBlockValue).prod) = 234899479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_3719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 234899479) ^ 117449739 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 234899479) ^ 78299826 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 234899479) ^ 21354498 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 234899479) ^ 8099982 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 234899479) ^ 63162 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_242612801 : Nat.Prime 242612801 := by
  apply lucas_primality 242612801 (3 : ZMod 242612801)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 2), (53, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 2), (53, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod) = 242612801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_53
      · exact prime_fiftyOneAW_2861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 242612801) ^ 121306400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 242612801) ^ 48522560 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 242612801) ^ 4577600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 242612801) ^ 84800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_250298611 : Nat.Prime 250298611 := by
  apply lucas_primality 250298611 (3 : ZMod 250298611)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1621, 1), (5147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1621, 1), (5147, 1)] : List FactorBlock).map factorBlockValue).prod) = 250298611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_1621
      · exact prime_fiftyOneAW_5147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 250298611) ^ 125149305 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 250298611) ^ 83432870 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 250298611) ^ 50059722 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 250298611) ^ 154410 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 250298611) ^ 48630 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_255334613 : Nat.Prime 255334613 := by
  apply lucas_primality 255334613 (2 : ZMod 255334613)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (677, 1), (7253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (677, 1), (7253, 1)] : List FactorBlock).map factorBlockValue).prod) = 255334613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_677
      · exact prime_fiftyOneAW_7253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 255334613) ^ 127667306 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 255334613) ^ 19641124 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 255334613) ^ 377156 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 255334613) ^ 35204 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_256258957 : Nat.Prime 256258957 := by
  apply lucas_primality 256258957 (5 : ZMod 256258957)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (21354913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (21354913, 1)] : List FactorBlock).map factorBlockValue).prod) = 256258957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_21354913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 256258957) ^ 128129478 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 256258957) ^ 85419652 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 256258957) ^ 12 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_256861039 : Nat.Prime 256861039 := by
  apply lucas_primality 256861039 (6 : ZMod 256861039)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (19, 1), (6569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (19, 1), (6569, 1)] : List FactorBlock).map factorBlockValue).prod) = 256861039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_6569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 256861039) ^ 128430519 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 256861039) ^ 85620346 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 256861039) ^ 36694434 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 256861039) ^ 13519002 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 256861039) ^ 39102 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_282861461 : Nat.Prime 282861461 := by
  apply lucas_primality 282861461 (2 : ZMod 282861461)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (41, 1), (49279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (41, 1), (49279, 1)] : List FactorBlock).map factorBlockValue).prod) = 282861461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_41
      · exact prime_fiftyOneAW_49279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 282861461) ^ 141430730 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 282861461) ^ 56572292 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 282861461) ^ 40408780 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 282861461) ^ 6899060 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 282861461) ^ 5740 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_288591263 : Nat.Prime 288591263 := by
  apply lucas_primality 288591263 (5 : ZMod 288591263)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (144295631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (144295631, 1)] : List FactorBlock).map factorBlockValue).prod) = 288591263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_144295631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 288591263) ^ 144295631 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 288591263) ^ 2 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_330134053 : Nat.Prime 330134053 := by
  apply lucas_primality 330134053 (6 : ZMod 330134053)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1657, 1), (16603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1657, 1), (16603, 1)] : List FactorBlock).map factorBlockValue).prod) = 330134053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_1657
      · exact prime_fiftyOneAW_16603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 330134053) ^ 165067026 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 330134053) ^ 110044684 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 330134053) ^ 199236 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 330134053) ^ 19884 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_344755493 : Nat.Prime 344755493 := by
  apply lucas_primality 344755493 (2 : ZMod 344755493)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (971, 1), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (971, 1), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) = 344755493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_37
      · exact prime_fiftyOneAW_971
      · exact prime_fiftyOneAW_2399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 344755493) ^ 172377746 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 344755493) ^ 9317716 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 344755493) ^ 355052 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 344755493) ^ 143708 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_344909167 : Nat.Prime 344909167 := by
  apply lucas_primality 344909167 (3 : ZMod 344909167)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (67, 1), (6451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (67, 1), (6451, 1)] : List FactorBlock).map factorBlockValue).prod) = 344909167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_67
      · exact prime_fiftyOneAW_6451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 344909167) ^ 172454583 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 344909167) ^ 114969722 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 344909167) ^ 49272738 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 344909167) ^ 18153114 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 344909167) ^ 5147898 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 344909167) ^ 53466 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_365755759 : Nat.Prime 365755759 := by
  apply lucas_primality 365755759 (3 : ZMod 365755759)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (60959293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (60959293, 1)] : List FactorBlock).map factorBlockValue).prod) = 365755759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_60959293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 365755759) ^ 182877879 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 365755759) ^ 121918586 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 365755759) ^ 6 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_393372509 : Nat.Prime 393372509 := by
  apply lucas_primality 393372509 (2 : ZMod 393372509)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (167, 1), (588881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (167, 1), (588881, 1)] : List FactorBlock).map factorBlockValue).prod) = 393372509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_167
      · exact prime_fiftyOneAW_588881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 393372509) ^ 196686254 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 393372509) ^ 2355524 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 393372509) ^ 668 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_405194327 : Nat.Prime 405194327 := by
  apply lucas_primality 405194327 (5 : ZMod 405194327)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (2339, 1), (2341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (2339, 1), (2341, 1)] : List FactorBlock).map factorBlockValue).prod) = 405194327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_37
      · exact prime_fiftyOneAW_2339
      · exact prime_fiftyOneAW_2341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 405194327) ^ 202597163 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 405194327) ^ 10951198 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 405194327) ^ 173234 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 405194327) ^ 173086 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_417516017 : Nat.Prime 417516017 := by
  apply lucas_primality 417516017 (3 : ZMod 417516017)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (113, 1), (7963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (113, 1), (7963, 1)] : List FactorBlock).map factorBlockValue).prod) = 417516017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_113
      · exact prime_fiftyOneAW_7963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 417516017) ^ 208758008 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 417516017) ^ 14397104 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 417516017) ^ 3694832 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 417516017) ^ 52432 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_505935631 : Nat.Prime 505935631 := by
  apply lucas_primality 505935631 (3 : ZMod 505935631)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (83, 1), (89, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (83, 1), (89, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) = 505935631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_83
      · exact prime_fiftyOneAW_89
      · exact prime_fiftyOneAW_761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 505935631) ^ 252967815 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 505935631) ^ 168645210 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 505935631) ^ 101187126 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 505935631) ^ 6095610 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 505935631) ^ 5684670 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 505935631) ^ 664830 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_530922851 : Nat.Prime 530922851 := by
  apply lucas_primality 530922851 (2 : ZMod 530922851)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (10618457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (10618457, 1)] : List FactorBlock).map factorBlockValue).prod) = 530922851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_10618457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 530922851) ^ 265461425 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 530922851) ^ 106184570 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 530922851) ^ 50 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_541894247 : Nat.Prime 541894247 := by
  apply lucas_primality 541894247 (5 : ZMod 541894247)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1303, 1), (207941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1303, 1), (207941, 1)] : List FactorBlock).map factorBlockValue).prod) = 541894247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_1303
      · exact prime_fiftyOneAW_207941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 541894247) ^ 270947123 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 541894247) ^ 415882 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 541894247) ^ 2606 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_547750043 : Nat.Prime 547750043 := by
  apply lucas_primality 547750043 (2 : ZMod 547750043)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (39125003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (39125003, 1)] : List FactorBlock).map factorBlockValue).prod) = 547750043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_39125003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 547750043) ^ 273875021 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 547750043) ^ 78250006 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 547750043) ^ 14 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_575558281 : Nat.Prime 575558281 := by
  apply lucas_primality 575558281 (29 : ZMod 575558281)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (11, 2), (73, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (11, 2), (73, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) = 575558281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_73
      · exact prime_fiftyOneAW_181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 575558281) ^ 287779140 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (29 : ZMod 575558281) ^ 191852760 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (29 : ZMod 575558281) ^ 115111656 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (29 : ZMod 575558281) ^ 52323480 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (29 : ZMod 575558281) ^ 7884360 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (29 : ZMod 575558281) ^ 3179880 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_680171353 : Nat.Prime 680171353 := by
  apply lucas_primality 680171353 (10 : ZMod 680171353)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (59, 1), (9803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (59, 1), (9803, 1)] : List FactorBlock).map factorBlockValue).prod) = 680171353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_59
      · exact prime_fiftyOneAW_9803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 680171353) ^ 340085676 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 680171353) ^ 226723784 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 680171353) ^ 97167336 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 680171353) ^ 11528328 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 680171353) ^ 69384 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_753004963 : Nat.Prime 753004963 := by
  apply lucas_primality 753004963 (2 : ZMod 753004963)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41833609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41833609, 1)] : List FactorBlock).map factorBlockValue).prod) = 753004963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_41833609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 753004963) ^ 376502481 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 753004963) ^ 251001654 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 753004963) ^ 18 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_774668639 : Nat.Prime 774668639 := by
  apply lucas_primality 774668639 (23 : ZMod 774668639)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (1663, 1), (2617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (1663, 1), (2617, 1)] : List FactorBlock).map factorBlockValue).prod) = 774668639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_89
      · exact prime_fiftyOneAW_1663
      · exact prime_fiftyOneAW_2617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 774668639) ^ 387334319 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (23 : ZMod 774668639) ^ 8704142 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (23 : ZMod 774668639) ^ 465826 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (23 : ZMod 774668639) ^ 296014 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1052072531 : Nat.Prime 1052072531 := by
  apply lucas_primality 1052072531 (6 : ZMod 1052072531)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (105207253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (105207253, 1)] : List FactorBlock).map factorBlockValue).prod) = 1052072531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_105207253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1052072531) ^ 526036265 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1052072531) ^ 210414506 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1052072531) ^ 10 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1184162741 : Nat.Prime 1184162741 := by
  apply lucas_primality 1184162741 (2 : ZMod 1184162741)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (887, 1), (66751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (887, 1), (66751, 1)] : List FactorBlock).map factorBlockValue).prod) = 1184162741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_887
      · exact prime_fiftyOneAW_66751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1184162741) ^ 592081370 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1184162741) ^ 236832548 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1184162741) ^ 1335020 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1184162741) ^ 17740 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1249741879 : Nat.Prime 1249741879 := by
  apply lucas_primality 1249741879 (6 : ZMod 1249741879)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (2705069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (2705069, 1)] : List FactorBlock).map factorBlockValue).prod) = 1249741879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_2705069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1249741879) ^ 624870939 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1249741879) ^ 416580626 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1249741879) ^ 178534554 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1249741879) ^ 113612898 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1249741879) ^ 462 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1275606721 : Nat.Prime 1275606721 := by
  apply lucas_primality 1275606721 (58 : ZMod 1275606721)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 1), (442919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 1), (442919, 1)] : List FactorBlock).map factorBlockValue).prod) = 1275606721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_442919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (58 : ZMod 1275606721) ^ 637803360 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (58 : ZMod 1275606721) ^ 425202240 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (58 : ZMod 1275606721) ^ 255121344 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (58 : ZMod 1275606721) ^ 2880 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1511443291 : Nat.Prime 1511443291 := by
  apply lucas_primality 1511443291 (19 : ZMod 1511443291)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (7197349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (7197349, 1)] : List FactorBlock).map factorBlockValue).prod) = 1511443291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_7197349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1511443291) ^ 755721645 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 1511443291) ^ 503814430 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 1511443291) ^ 302288658 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 1511443291) ^ 215920470 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 1511443291) ^ 210 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1531464617 : Nat.Prime 1531464617 := by
  apply lucas_primality 1531464617 (3 : ZMod 1531464617)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (101, 1), (172307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (101, 1), (172307, 1)] : List FactorBlock).map factorBlockValue).prod) = 1531464617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_101
      · exact prime_fiftyOneAW_172307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1531464617) ^ 765732308 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1531464617) ^ 139224056 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1531464617) ^ 15163016 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1531464617) ^ 8888 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1588277671 : Nat.Prime 1588277671 := by
  apply lucas_primality 1588277671 (7 : ZMod 1588277671)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (43, 1), (25127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (43, 1), (25127, 1)] : List FactorBlock).map factorBlockValue).prod) = 1588277671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_43
      · exact prime_fiftyOneAW_25127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1588277671) ^ 794138835 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1588277671) ^ 529425890 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1588277671) ^ 317655534 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1588277671) ^ 226896810 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1588277671) ^ 36936690 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1588277671) ^ 63210 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1688112793 : Nat.Prime 1688112793 := by
  apply lucas_primality 1688112793 (5 : ZMod 1688112793)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7815337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7815337, 1)] : List FactorBlock).map factorBlockValue).prod) = 1688112793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7815337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1688112793) ^ 844056396 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1688112793) ^ 562704264 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1688112793) ^ 216 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1898759389 : Nat.Prime 1898759389 := by
  apply lucas_primality 1898759389 (2 : ZMod 1898759389)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (307, 1), (22409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (307, 1), (22409, 1)] : List FactorBlock).map factorBlockValue).prod) = 1898759389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_307
      · exact prime_fiftyOneAW_22409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1898759389) ^ 949379694 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1898759389) ^ 632919796 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1898759389) ^ 82554756 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1898759389) ^ 6184884 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1898759389) ^ 84732 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1968350653 : Nat.Prime 1968350653 := by
  apply lucas_primality 1968350653 (6 : ZMod 1968350653)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (18225469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (18225469, 1)] : List FactorBlock).map factorBlockValue).prod) = 1968350653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_18225469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1968350653) ^ 984175326 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1968350653) ^ 656116884 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1968350653) ^ 108 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_2179651489 : Nat.Prime 2179651489 := by
  apply lucas_primality 2179651489 (19 : ZMod 2179651489)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (23, 1), (141023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (23, 1), (141023, 1)] : List FactorBlock).map factorBlockValue).prod) = 2179651489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_141023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 2179651489) ^ 1089825744 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 2179651489) ^ 726550496 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 2179651489) ^ 311378784 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 2179651489) ^ 94767456 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 2179651489) ^ 15456 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_2367164141 : Nat.Prime 2367164141 := by
  apply lucas_primality 2367164141 (7 : ZMod 2367164141)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 2), (23, 1), (71, 1), (599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 2), (23, 1), (71, 1), (599, 1)] : List FactorBlock).map factorBlockValue).prod) = 2367164141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_71
      · exact prime_fiftyOneAW_599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2367164141) ^ 1183582070 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2367164141) ^ 473432828 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2367164141) ^ 215196740 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2367164141) ^ 102920180 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2367164141) ^ 33340340 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2367164141) ^ 3951860 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_2844681403 : Nat.Prime 2844681403 := by
  apply lucas_primality 2844681403 (2 : ZMod 2844681403)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (937, 1), (9547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (937, 1), (9547, 1)] : List FactorBlock).map factorBlockValue).prod) = 2844681403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_53
      · exact prime_fiftyOneAW_937
      · exact prime_fiftyOneAW_9547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2844681403) ^ 1422340701 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2844681403) ^ 948227134 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2844681403) ^ 53673234 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2844681403) ^ 3035946 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2844681403) ^ 297966 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_2993597287 : Nat.Prime 2993597287 := by
  apply lucas_primality 2993597287 (3 : ZMod 2993597287)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (73, 1), (337, 1), (1193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (73, 1), (337, 1), (1193, 1)] : List FactorBlock).map factorBlockValue).prod) = 2993597287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_73
      · exact prime_fiftyOneAW_337
      · exact prime_fiftyOneAW_1193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2993597287) ^ 1496798643 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2993597287) ^ 997865762 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2993597287) ^ 176093958 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2993597287) ^ 41008182 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2993597287) ^ 8883078 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2993597287) ^ 2509302 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_3385416493 : Nat.Prime 3385416493 := by
  apply lucas_primality 3385416493 (14 : ZMod 3385416493)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (31346449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (31346449, 1)] : List FactorBlock).map factorBlockValue).prod) = 3385416493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_31346449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 3385416493) ^ 1692708246 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (14 : ZMod 3385416493) ^ 1128472164 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (14 : ZMod 3385416493) ^ 108 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_3410303987 : Nat.Prime 3410303987 := by
  apply lucas_primality 3410303987 (5 : ZMod 3410303987)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (37, 1), (41, 1), (101, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (37, 1), (41, 1), (101, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) = 3410303987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_31
      · exact prime_fiftyOneAW_37
      · exact prime_fiftyOneAW_41
      · exact prime_fiftyOneAW_101
      · exact prime_fiftyOneAW_359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3410303987) ^ 1705151993 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3410303987) ^ 110009806 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3410303987) ^ 92170378 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3410303987) ^ 83178146 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3410303987) ^ 33765386 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3410303987) ^ 9499454 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_3540386347 : Nat.Prime 3540386347 := by
  apply lucas_primality 3540386347 (11 : ZMod 3540386347)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod) = 3540386347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3540386347) ^ 1770193173 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 1180128782 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 505769478 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 42 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_3880233977 : Nat.Prime 3880233977 := by
  apply lucas_primality 3880233977 (3 : ZMod 3880233977)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2287, 1), (212081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2287, 1), (212081, 1)] : List FactorBlock).map factorBlockValue).prod) = 3880233977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_2287
      · exact prime_fiftyOneAW_212081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3880233977) ^ 1940116988 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3880233977) ^ 1696648 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3880233977) ^ 18296 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_4398554527 : Nat.Prime 4398554527 := by
  apply lucas_primality 4398554527 (5 : ZMod 4398554527)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (25279049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (25279049, 1)] : List FactorBlock).map factorBlockValue).prod) = 4398554527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_25279049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4398554527) ^ 2199277263 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4398554527) ^ 1466184842 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4398554527) ^ 151674294 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4398554527) ^ 174 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_4594920691 : Nat.Prime 4594920691 := by
  apply lucas_primality 4594920691 (10 : ZMod 4594920691)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (47, 1), (461, 1), (7069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (47, 1), (461, 1), (7069, 1)] : List FactorBlock).map factorBlockValue).prod) = 4594920691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_47
      · exact prime_fiftyOneAW_461
      · exact prime_fiftyOneAW_7069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 4594920691) ^ 2297460345 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 4594920691) ^ 1531640230 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 4594920691) ^ 918984138 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 4594920691) ^ 97764270 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 4594920691) ^ 9967290 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 4594920691) ^ 650010 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_5082168359 : Nat.Prime 5082168359 := by
  apply lucas_primality 5082168359 (7 : ZMod 5082168359)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (14196001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (14196001, 1)] : List FactorBlock).map factorBlockValue).prod) = 5082168359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_179
      · exact prime_fiftyOneAW_14196001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 5082168359) ^ 2541084179 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 5082168359) ^ 28392002 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 5082168359) ^ 358 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_5543017387 : Nat.Prime 5543017387 := by
  apply lucas_primality 5543017387 (2 : ZMod 5543017387)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (83, 1), (401, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (83, 1), (401, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 5543017387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_41
      · exact prime_fiftyOneAW_83
      · exact prime_fiftyOneAW_401
      · exact prime_fiftyOneAW_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5543017387) ^ 2771508693 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5543017387) ^ 1847672462 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5543017387) ^ 135195546 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5543017387) ^ 66783342 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5543017387) ^ 13822986 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5543017387) ^ 8187618 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_6180542191 : Nat.Prime 6180542191 := by
  apply lucas_primality 6180542191 (6 : ZMod 6180542191)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (5, 1), (71, 1), (11941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (5, 1), (71, 1), (11941, 1)] : List FactorBlock).map factorBlockValue).prod) = 6180542191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_71
      · exact prime_fiftyOneAW_11941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 6180542191) ^ 3090271095 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 6180542191) ^ 2060180730 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 6180542191) ^ 1236108438 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 6180542191) ^ 87049890 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 6180542191) ^ 517590 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_6391408799 : Nat.Prime 6391408799 := by
  apply lucas_primality 6391408799 (23 : ZMod 6391408799)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod) = 6391408799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_89
      · exact prime_fiftyOneAW_223
      · exact prime_fiftyOneAW_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 6391408799) ^ 3195704399 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 71813582 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 28661026 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 39694 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_6802865389 : Nat.Prime 6802865389 := by
  apply lucas_primality 6802865389 (2 : ZMod 6802865389)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 2), (23, 1), (67901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 2), (23, 1), (67901, 1)] : List FactorBlock).map factorBlockValue).prod) = 6802865389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_67901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6802865389) ^ 3401432694 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6802865389) ^ 2267621796 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6802865389) ^ 618442308 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6802865389) ^ 295776756 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6802865389) ^ 100188 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_6886286111 : Nat.Prime 6886286111 := by
  apply lucas_primality 6886286111 (11 : ZMod 6886286111)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (62602601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (62602601, 1)] : List FactorBlock).map factorBlockValue).prod) = 6886286111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_62602601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 6886286111) ^ 3443143055 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 6886286111) ^ 1377257222 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 6886286111) ^ 626026010 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 6886286111) ^ 110 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_7586519459 : Nat.Prime 7586519459 := by
  apply lucas_primality 7586519459 (2 : ZMod 7586519459)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (541894247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (541894247, 1)] : List FactorBlock).map factorBlockValue).prod) = 7586519459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_541894247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7586519459) ^ 3793259729 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7586519459) ^ 1083788494 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7586519459) ^ 14 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_8766968939 : Nat.Prime 8766968939 := by
  apply lucas_primality 8766968939 (2 : ZMod 8766968939)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (47, 1), (137, 1), (7481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (47, 1), (137, 1), (7481, 1)] : List FactorBlock).map factorBlockValue).prod) = 8766968939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_47
      · exact prime_fiftyOneAW_137
      · exact prime_fiftyOneAW_7481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8766968939) ^ 4383484469 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8766968939) ^ 1252424134 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8766968939) ^ 674382226 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8766968939) ^ 186531254 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8766968939) ^ 63992474 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8766968939) ^ 1171898 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_9277522589 : Nat.Prime 9277522589 := by
  apply lucas_primality 9277522589 (2 : ZMod 9277522589)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod) = 9277522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_53
      · exact prime_fiftyOneAW_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9277522589) ^ 4638761294 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 319914572 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 175047596 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 6148 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_9564358091 : Nat.Prime 9564358091 := by
  apply lucas_primality 9564358091 (2 : ZMod 9564358091)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (83, 1), (1646189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (83, 1), (1646189, 1)] : List FactorBlock).map factorBlockValue).prod) = 9564358091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_83
      · exact prime_fiftyOneAW_1646189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9564358091) ^ 4782179045 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9564358091) ^ 1912871618 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9564358091) ^ 1366336870 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9564358091) ^ 115233230 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9564358091) ^ 5810 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_11747183939 : Nat.Prime 11747183939 := by
  apply lucas_primality 11747183939 (2 : ZMod 11747183939)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (521, 1), (1610527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (521, 1), (1610527, 1)] : List FactorBlock).map factorBlockValue).prod) = 11747183939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_521
      · exact prime_fiftyOneAW_1610527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11747183939) ^ 5873591969 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11747183939) ^ 1678169134 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11747183939) ^ 22547378 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11747183939) ^ 7294 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_12048401357 : Nat.Prime 12048401357 := by
  apply lucas_primality 12048401357 (2 : ZMod 12048401357)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (263, 1), (11452853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (263, 1), (11452853, 1)] : List FactorBlock).map factorBlockValue).prod) = 12048401357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_263
      · exact prime_fiftyOneAW_11452853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12048401357) ^ 6024200678 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12048401357) ^ 45811412 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12048401357) ^ 1052 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_14093968741 : Nat.Prime 14093968741 := by
  apply lucas_primality 14093968741 (7 : ZMod 14093968741)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (234899479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (234899479, 1)] : List FactorBlock).map factorBlockValue).prod) = 14093968741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_234899479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 14093968741) ^ 7046984370 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 14093968741) ^ 4697989580 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 14093968741) ^ 2818793748 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 14093968741) ^ 60 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_15173038919 : Nat.Prime 15173038919 := by
  apply lucas_primality 15173038919 (11 : ZMod 15173038919)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7586519459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7586519459, 1)] : List FactorBlock).map factorBlockValue).prod) = 15173038919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_7586519459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 15173038919) ^ 7586519459 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 15173038919) ^ 2 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_15399368939 : Nat.Prime 15399368939 := by
  apply lucas_primality 15399368939 (2 : ZMod 15399368939)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (29, 1), (13974019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (29, 1), (13974019, 1)] : List FactorBlock).map factorBlockValue).prod) = 15399368939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_13974019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15399368939) ^ 7699684469 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15399368939) ^ 810493102 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15399368939) ^ 531012722 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15399368939) ^ 1102 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_15501321547 : Nat.Prime 15501321547 := by
  apply lucas_primality 15501321547 (2 : ZMod 15501321547)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1103, 1), (101839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1103, 1), (101839, 1)] : List FactorBlock).map factorBlockValue).prod) = 15501321547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_1103
      · exact prime_fiftyOneAW_101839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15501321547) ^ 7750660773 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15501321547) ^ 5167107182 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15501321547) ^ 673970502 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15501321547) ^ 14053782 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15501321547) ^ 152214 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_20699526191 : Nat.Prime 20699526191 := by
  apply lucas_primality 20699526191 (7 : ZMod 20699526191)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (43, 1), (109, 1), (9013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (43, 1), (109, 1), (9013, 1)] : List FactorBlock).map factorBlockValue).prod) = 20699526191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_43
      · exact prime_fiftyOneAW_109
      · exact prime_fiftyOneAW_9013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20699526191) ^ 10349763095 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 20699526191) ^ 4139905238 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 20699526191) ^ 2957075170 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 20699526191) ^ 481384330 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 20699526191) ^ 189903910 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 20699526191) ^ 2296630 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_21764550497 : Nat.Prime 21764550497 := by
  apply lucas_primality 21764550497 (3 : ZMod 21764550497)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (151, 1), (317, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (151, 1), (317, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) = 21764550497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_151
      · exact prime_fiftyOneAW_317
      · exact prime_fiftyOneAW_1093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21764550497) ^ 10882275248 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 21764550497) ^ 1674196192 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 21764550497) ^ 144136096 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 21764550497) ^ 68657888 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 21764550497) ^ 19912672 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_21934177247 : Nat.Prime 21934177247 := by
  apply lucas_primality 21934177247 (5 : ZMod 21934177247)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1279, 1), (8574737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1279, 1), (8574737, 1)] : List FactorBlock).map factorBlockValue).prod) = 21934177247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_1279
      · exact prime_fiftyOneAW_8574737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 21934177247) ^ 10967088623 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 21934177247) ^ 17149474 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 21934177247) ^ 2558 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_23601876497 : Nat.Prime 23601876497 := by
  apply lucas_primality 23601876497 (3 : ZMod 23601876497)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (103, 1), (1301957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (103, 1), (1301957, 1)] : List FactorBlock).map factorBlockValue).prod) = 23601876497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_103
      · exact prime_fiftyOneAW_1301957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 23601876497) ^ 11800938248 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 23601876497) ^ 2145625136 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 23601876497) ^ 229144432 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 23601876497) ^ 18128 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_30158010563 : Nat.Prime 30158010563 := by
  apply lucas_primality 30158010563 (2 : ZMod 30158010563)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (140925283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (140925283, 1)] : List FactorBlock).map factorBlockValue).prod) = 30158010563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_107
      · exact prime_fiftyOneAW_140925283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30158010563) ^ 15079005281 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30158010563) ^ 281850566 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30158010563) ^ 214 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_30429025931 : Nat.Prime 30429025931 := by
  apply lucas_primality 30429025931 (2 : ZMod 30429025931)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod) = 30429025931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_71
      · exact prime_fiftyOneAW_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30429025931) ^ 15214512965 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 6085805186 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 428577830 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 710 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_38348615209 : Nat.Prime 38348615209 := by
  apply lucas_primality 38348615209 (13 : ZMod 38348615209)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (73, 1), (173, 1), (5501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (73, 1), (173, 1), (5501, 1)] : List FactorBlock).map factorBlockValue).prod) = 38348615209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_73
      · exact prime_fiftyOneAW_173
      · exact prime_fiftyOneAW_5501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 38348615209) ^ 19174307604 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (13 : ZMod 38348615209) ^ 12782871736 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (13 : ZMod 38348615209) ^ 1667331096 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (13 : ZMod 38348615209) ^ 525323496 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (13 : ZMod 38348615209) ^ 221668296 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (13 : ZMod 38348615209) ^ 6971208 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_39568669331 : Nat.Prime 39568669331 := by
  apply lucas_primality 39568669331 (2 : ZMod 39568669331)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1097, 1), (3606989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1097, 1), (3606989, 1)] : List FactorBlock).map factorBlockValue).prod) = 39568669331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_1097
      · exact prime_fiftyOneAW_3606989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39568669331) ^ 19784334665 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 39568669331) ^ 7913733866 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 39568669331) ^ 36069890 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 39568669331) ^ 10970 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_40760672467 : Nat.Prime 40760672467 := by
  apply lucas_primality 40760672467 (5 : ZMod 40760672467)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (179, 1), (37952209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (179, 1), (37952209, 1)] : List FactorBlock).map factorBlockValue).prod) = 40760672467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_179
      · exact prime_fiftyOneAW_37952209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 40760672467) ^ 20380336233 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 40760672467) ^ 13586890822 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 40760672467) ^ 227713254 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 40760672467) ^ 1074 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_45343298731 : Nat.Prime 45343298731 := by
  apply lucas_primality 45343298731 (2 : ZMod 45343298731)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1511443291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1511443291, 1)] : List FactorBlock).map factorBlockValue).prod) = 45343298731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_1511443291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45343298731) ^ 22671649365 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45343298731) ^ 15114432910 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45343298731) ^ 9068659746 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45343298731) ^ 30 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_49153528429 : Nat.Prime 49153528429 := by
  apply lucas_primality 49153528429 (2 : ZMod 49153528429)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (61, 1), (1061, 1), (3331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (61, 1), (1061, 1), (3331, 1)] : List FactorBlock).map factorBlockValue).prod) = 49153528429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_61
      · exact prime_fiftyOneAW_1061
      · exact prime_fiftyOneAW_3331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49153528429) ^ 24576764214 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 49153528429) ^ 16384509476 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 49153528429) ^ 2587027812 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 49153528429) ^ 805795548 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 49153528429) ^ 46327548 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 49153528429) ^ 14756388 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_64157931401 : Nat.Prime 64157931401 := by
  apply lucas_primality 64157931401 (3 : ZMod 64157931401)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (191, 1), (761, 1), (2207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (191, 1), (761, 1), (2207, 1)] : List FactorBlock).map factorBlockValue).prod) = 64157931401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_191
      · exact prime_fiftyOneAW_761
      · exact prime_fiftyOneAW_2207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 64157931401) ^ 32078965700 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 64157931401) ^ 12831586280 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 64157931401) ^ 335905400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 64157931401) ^ 84307400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 64157931401) ^ 29070200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_65984608471 : Nat.Prime 65984608471 := by
  apply lucas_primality 65984608471 (3 : ZMod 65984608471)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (967, 1), (10883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (967, 1), (10883, 1)] : List FactorBlock).map factorBlockValue).prod) = 65984608471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_967
      · exact prime_fiftyOneAW_10883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65984608471) ^ 32992304235 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 65984608471) ^ 21994869490 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 65984608471) ^ 13196921694 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 65984608471) ^ 5998600770 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 65984608471) ^ 3472874130 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 65984608471) ^ 68236410 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 65984608471) ^ 6063090 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_80091080543 : Nat.Prime 80091080543 := by
  apply lucas_primality 80091080543 (5 : ZMod 80091080543)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (29, 1), (10267, 1), (12227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (29, 1), (10267, 1), (12227, 1)] : List FactorBlock).map factorBlockValue).prod) = 80091080543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_10267
      · exact prime_fiftyOneAW_12227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 80091080543) ^ 40045540271 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 80091080543) ^ 7281007322 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 80091080543) ^ 2761761398 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 80091080543) ^ 7800826 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 80091080543) ^ 6550346 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_111000841031 : Nat.Prime 111000841031 := by
  apply lucas_primality 111000841031 (11 : ZMod 111000841031)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (9497, 1), (1168799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (9497, 1), (1168799, 1)] : List FactorBlock).map factorBlockValue).prod) = 111000841031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_9497
      · exact prime_fiftyOneAW_1168799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 111000841031) ^ 55500420515 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 111000841031) ^ 22200168206 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 111000841031) ^ 11687990 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 111000841031) ^ 94970 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_111179436971 : Nat.Prime 111179436971 := by
  apply lucas_primality 111179436971 (2 : ZMod 111179436971)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (1588277671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (1588277671, 1)] : List FactorBlock).map factorBlockValue).prod) = 111179436971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_1588277671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 111179436971) ^ 55589718485 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 111179436971) ^ 22235887394 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 111179436971) ^ 15882776710 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 111179436971) ^ 70 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_118581886303 : Nat.Prime 118581886303 := by
  apply lucas_primality 118581886303 (6 : ZMod 118581886303)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (37, 1), (241, 1), (201491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (37, 1), (241, 1), (201491, 1)] : List FactorBlock).map factorBlockValue).prod) = 118581886303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_37
      · exact prime_fiftyOneAW_241
      · exact prime_fiftyOneAW_201491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 118581886303) ^ 59290943151 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 118581886303) ^ 39527295434 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 118581886303) ^ 10780171482 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 118581886303) ^ 3204915846 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 118581886303) ^ 492041022 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 118581886303) ^ 588522 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_122684585791 : Nat.Prime 122684585791 := by
  apply lucas_primality 122684585791 (6 : ZMod 122684585791)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (1051, 1), (299311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (1051, 1), (299311, 1)] : List FactorBlock).map factorBlockValue).prod) = 122684585791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_1051
      · exact prime_fiftyOneAW_299311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 122684585791) ^ 61342292895 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 122684585791) ^ 40894861930 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 122684585791) ^ 24536917158 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 122684585791) ^ 9437275830 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 122684585791) ^ 116731290 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 122684585791) ^ 409890 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_129009340363 : Nat.Prime 129009340363 := by
  apply lucas_primality 129009340363 (2 : ZMod 129009340363)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (9829, 1), (312509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (9829, 1), (312509, 1)] : List FactorBlock).map factorBlockValue).prod) = 129009340363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_9829
      · exact prime_fiftyOneAW_312509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 129009340363) ^ 64504670181 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 129009340363) ^ 43003113454 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 129009340363) ^ 18429905766 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 129009340363) ^ 13125378 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 129009340363) ^ 412818 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_146634385643 : Nat.Prime 146634385643 := by
  apply lucas_primality 146634385643 (2 : ZMod 146634385643)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (187477, 1), (391073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (187477, 1), (391073, 1)] : List FactorBlock).map factorBlockValue).prod) = 146634385643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_187477
      · exact prime_fiftyOneAW_391073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 146634385643) ^ 73317192821 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 146634385643) ^ 782146 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 146634385643) ^ 374954 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_163694591377 : Nat.Prime 163694591377 := by
  apply lucas_primality 163694591377 (5 : ZMod 163694591377)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (3410303987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (3410303987, 1)] : List FactorBlock).map factorBlockValue).prod) = 163694591377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_3410303987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 163694591377) ^ 81847295688 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 163694591377) ^ 54564863792 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 163694591377) ^ 48 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_182885059769 : Nat.Prime 182885059769 := by
  apply lucas_primality 182885059769 (3 : ZMod 182885059769)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (89, 1), (256861039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (89, 1), (256861039, 1)] : List FactorBlock).map factorBlockValue).prod) = 182885059769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_89
      · exact prime_fiftyOneAW_256861039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 182885059769) ^ 91442529884 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 182885059769) ^ 2054888312 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 182885059769) ^ 712 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_202458184399 : Nat.Prime 202458184399 := by
  apply lucas_primality 202458184399 (3 : ZMod 202458184399)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (1249741879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (1249741879, 1)] : List FactorBlock).map factorBlockValue).prod) = 202458184399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_1249741879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 202458184399) ^ 101229092199 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 202458184399) ^ 67486061466 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 202458184399) ^ 162 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_262367120149 : Nat.Prime 262367120149 := by
  apply lucas_primality 262367120149 (14 : ZMod 262367120149)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (727, 1), (1069, 1), (4019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (727, 1), (1069, 1), (4019, 1)] : List FactorBlock).map factorBlockValue).prod) = 262367120149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_727
      · exact prime_fiftyOneAW_1069
      · exact prime_fiftyOneAW_4019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 262367120149) ^ 131183560074 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (14 : ZMod 262367120149) ^ 87455706716 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (14 : ZMod 262367120149) ^ 37481017164 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (14 : ZMod 262367120149) ^ 360890124 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (14 : ZMod 262367120149) ^ 245432292 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (14 : ZMod 262367120149) ^ 65281692 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_277508030299 : Nat.Prime 277508030299 := by
  apply lucas_primality 277508030299 (3 : ZMod 277508030299)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod) = 277508030299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_149
      · exact prime_fiftyOneAW_1429
      · exact prime_fiftyOneAW_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277508030299) ^ 138754015149 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 92502676766 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1862470002 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 194197362 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1277526 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_338021059213 : Nat.Prime 338021059213 := by
  apply lucas_primality 338021059213 (2 : ZMod 338021059213)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (67, 1), (227, 1), (617363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (67, 1), (227, 1), (617363, 1)] : List FactorBlock).map factorBlockValue).prod) = 338021059213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_67
      · exact prime_fiftyOneAW_227
      · exact prime_fiftyOneAW_617363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 338021059213) ^ 169010529606 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 338021059213) ^ 112673686404 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 338021059213) ^ 5045090436 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 338021059213) ^ 1489079556 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 338021059213) ^ 547524 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_395043748273 : Nat.Prime 395043748273 := by
  apply lucas_primality 395043748273 (5 : ZMod 395043748273)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (1871, 1), (162917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (1871, 1), (162917, 1)] : List FactorBlock).map factorBlockValue).prod) = 395043748273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_1871
      · exact prime_fiftyOneAW_162917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 395043748273) ^ 197521874136 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 395043748273) ^ 131681249424 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 395043748273) ^ 211140432 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 395043748273) ^ 2424816 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_430786049731 : Nat.Prime 430786049731 := by
  apply lucas_primality 430786049731 (2 : ZMod 430786049731)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (59, 1), (8392481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (59, 1), (8392481, 1)] : List FactorBlock).map factorBlockValue).prod) = 430786049731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_59
      · exact prime_fiftyOneAW_8392481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 430786049731) ^ 215393024865 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 430786049731) ^ 143595349910 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 430786049731) ^ 86157209946 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 430786049731) ^ 14854691370 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 430786049731) ^ 7301458470 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 430786049731) ^ 51330 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_504121961207 : Nat.Prime 504121961207 := by
  apply lucas_primality 504121961207 (5 : ZMod 504121961207)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (277, 1), (461, 1), (32359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (277, 1), (461, 1), (32359, 1)] : List FactorBlock).map factorBlockValue).prod) = 504121961207 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_61
      · exact prime_fiftyOneAW_277
      · exact prime_fiftyOneAW_461
      · exact prime_fiftyOneAW_32359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 504121961207) ^ 252060980603 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 504121961207) ^ 8264294446 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 504121961207) ^ 1819934878 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 504121961207) ^ 1093540046 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 504121961207) ^ 15579034 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_556248797191 : Nat.Prime 556248797191 := by
  apply lucas_primality 556248797191 (3 : ZMod 556248797191)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (6180542191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (6180542191, 1)] : List FactorBlock).map factorBlockValue).prod) = 556248797191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_6180542191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 556248797191) ^ 278124398595 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 556248797191) ^ 185416265730 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 556248797191) ^ 111249759438 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 556248797191) ^ 90 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_654778365509 : Nat.Prime 654778365509 := by
  apply lucas_primality 654778365509 (2 : ZMod 654778365509)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (163694591377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (163694591377, 1)] : List FactorBlock).map factorBlockValue).prod) = 654778365509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_163694591377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 654778365509) ^ 327389182754 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 654778365509) ^ 4 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_878586350657 : Nat.Prime 878586350657 := by
  apply lucas_primality 878586350657 (5 : ZMod 878586350657)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (263, 1), (7456769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (263, 1), (7456769, 1)] : List FactorBlock).map factorBlockValue).prod) = 878586350657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_263
      · exact prime_fiftyOneAW_7456769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 878586350657) ^ 439293175328 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 878586350657) ^ 125512335808 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 878586350657) ^ 3340632512 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 878586350657) ^ 117824 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_964862349257 : Nat.Prime 964862349257 := by
  apply lucas_primality 964862349257 (5 : ZMod 964862349257)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod) = 964862349257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 964862349257) ^ 482431174628 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 74220180712 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 104 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_977525475497 : Nat.Prime 977525475497 := by
  apply lucas_primality 977525475497 (3 : ZMod 977525475497)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1097, 1), (111386221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1097, 1), (111386221, 1)] : List FactorBlock).map factorBlockValue).prod) = 977525475497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_1097
      · exact prime_fiftyOneAW_111386221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 977525475497) ^ 488762737748 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 977525475497) ^ 891089768 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 977525475497) ^ 8776 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_35279
      · exact prime_fiftyOneAW_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1728403954313 : Nat.Prime 1728403954313 := by
  apply lucas_primality 1728403954313 (3 : ZMod 1728403954313)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 3), (281, 1), (2241583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 3), (281, 1), (2241583, 1)] : List FactorBlock).map factorBlockValue).prod) = 1728403954313 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_281
      · exact prime_fiftyOneAW_2241583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1728403954313) ^ 864201977156 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1728403954313) ^ 246914850616 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1728403954313) ^ 6150903752 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1728403954313) ^ 771064 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1830580643707 : Nat.Prime 1830580643707 := by
  apply lucas_primality 1830580643707 (2 : ZMod 1830580643707)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (557, 1), (547750043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (557, 1), (547750043, 1)] : List FactorBlock).map factorBlockValue).prod) = 1830580643707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_557
      · exact prime_fiftyOneAW_547750043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1830580643707) ^ 915290321853 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1830580643707) ^ 610193547902 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1830580643707) ^ 3286500258 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1830580643707) ^ 3342 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_2189453993149 : Nat.Prime 2189453993149 := by
  apply lucas_primality 2189453993149 (6 : ZMod 2189453993149)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (23, 1), (417516017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (23, 1), (417516017, 1)] : List FactorBlock).map factorBlockValue).prod) = 2189453993149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_417516017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2189453993149) ^ 1094726996574 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2189453993149) ^ 729817997716 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2189453993149) ^ 115234420692 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2189453993149) ^ 95193651876 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2189453993149) ^ 5244 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_2661052133353 : Nat.Prime 2661052133353 := by
  apply lucas_primality 2661052133353 (5 : ZMod 2661052133353)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (71, 1), (647, 1), (2413679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (71, 1), (647, 1), (2413679, 1)] : List FactorBlock).map factorBlockValue).prod) = 2661052133353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_71
      · exact prime_fiftyOneAW_647
      · exact prime_fiftyOneAW_2413679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2661052133353) ^ 1330526066676 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2661052133353) ^ 887017377784 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2661052133353) ^ 37479607512 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2661052133353) ^ 4112909016 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2661052133353) ^ 1102488 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_4065433399897 : Nat.Prime 4065433399897 := by
  apply lucas_primality 4065433399897 (10 : ZMod 4065433399897)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (15399368939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (15399368939, 1)] : List FactorBlock).map factorBlockValue).prod) = 4065433399897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_15399368939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 4065433399897) ^ 2032716699948 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 4065433399897) ^ 1355144466632 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 4065433399897) ^ 369584854536 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 4065433399897) ^ 264 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_6126952389931 : Nat.Prime 6126952389931 := by
  apply lucas_primality 6126952389931 (2 : ZMod 6126952389931)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (113, 1), (5657, 1), (11833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (113, 1), (5657, 1), (11833, 1)] : List FactorBlock).map factorBlockValue).prod) = 6126952389931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_113
      · exact prime_fiftyOneAW_5657
      · exact prime_fiftyOneAW_11833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6126952389931) ^ 3063476194965 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6126952389931) ^ 2042317463310 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6126952389931) ^ 1225390477986 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6126952389931) ^ 54220817610 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6126952389931) ^ 1083074490 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6126952389931) ^ 517785210 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_6708485698877 : Nat.Prime 6708485698877 := by
  apply lucas_primality 6708485698877 (2 : ZMod 6708485698877)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (129009340363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (129009340363, 1)] : List FactorBlock).map factorBlockValue).prod) = 6708485698877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_129009340363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6708485698877) ^ 3354242849438 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6708485698877) ^ 516037361452 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6708485698877) ^ 52 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_7244372988773 : Nat.Prime 7244372988773 := by
  apply lucas_primality 7244372988773 (2 : ZMod 7244372988773)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (263, 1), (6886286111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (263, 1), (6886286111, 1)] : List FactorBlock).map factorBlockValue).prod) = 7244372988773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_263
      · exact prime_fiftyOneAW_6886286111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7244372988773) ^ 3622186494386 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7244372988773) ^ 27545144444 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7244372988773) ^ 1052 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_7820203803977 : Nat.Prime 7820203803977 := by
  apply lucas_primality 7820203803977 (3 : ZMod 7820203803977)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (977525475497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (977525475497, 1)] : List FactorBlock).map factorBlockValue).prod) = 7820203803977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_977525475497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 7820203803977) ^ 3910101901988 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7820203803977) ^ 8 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_7908989265053 : Nat.Prime 7908989265053 := by
  apply lucas_primality 7908989265053 (2 : ZMod 7908989265053)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (167, 1), (6397, 1), (1850837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (167, 1), (6397, 1), (1850837, 1)] : List FactorBlock).map factorBlockValue).prod) = 7908989265053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_167
      · exact prime_fiftyOneAW_6397
      · exact prime_fiftyOneAW_1850837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7908989265053) ^ 3954494632526 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7908989265053) ^ 47359217156 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7908989265053) ^ 1236359116 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7908989265053) ^ 4273196 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_7953071166697 : Nat.Prime 7953071166697 := by
  apply lucas_primality 7953071166697 (5 : ZMod 7953071166697)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (19, 1), (191, 1), (5371403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (19, 1), (191, 1), (5371403, 1)] : List FactorBlock).map factorBlockValue).prod) = 7953071166697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_191
      · exact prime_fiftyOneAW_5371403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7953071166697) ^ 3976535583348 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 7953071166697) ^ 2651023722232 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 7953071166697) ^ 467827715688 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 7953071166697) ^ 418582692984 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 7953071166697) ^ 41639116056 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 7953071166697) ^ 1480632 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_11090280900929 : Nat.Prime 11090280900929 := by
  apply lucas_primality 11090280900929 (3 : ZMod 11090280900929)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (47, 1), (127, 1), (1601, 1), (18133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (47, 1), (127, 1), (1601, 1), (18133, 1)] : List FactorBlock).map factorBlockValue).prod) = 11090280900929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_47
      · exact prime_fiftyOneAW_127
      · exact prime_fiftyOneAW_1601
      · exact prime_fiftyOneAW_18133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11090280900929) ^ 5545140450464 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 11090280900929) ^ 235963423424 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 11090280900929) ^ 87325046464 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 11090280900929) ^ 6927096128 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 11090280900929) ^ 611607616 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_11492716013243 : Nat.Prime 11492716013243 := by
  apply lucas_primality 11492716013243 (2 : ZMod 11492716013243)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (338021059213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (338021059213, 1)] : List FactorBlock).map factorBlockValue).prod) = 11492716013243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_338021059213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11492716013243) ^ 5746358006621 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11492716013243) ^ 676042118426 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11492716013243) ^ 34 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_15094119245369 : Nat.Prime 15094119245369 := by
  apply lucas_primality 15094119245369 (3 : ZMod 15094119245369)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (71, 1), (1091, 1), (24357611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (71, 1), (1091, 1), (24357611, 1)] : List FactorBlock).map factorBlockValue).prod) = 15094119245369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_71
      · exact prime_fiftyOneAW_1091
      · exact prime_fiftyOneAW_24357611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 15094119245369) ^ 7547059622684 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 15094119245369) ^ 212593228808 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 15094119245369) ^ 13835123048 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 15094119245369) ^ 619688 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_16516893739069 : Nat.Prime 16516893739069 := by
  apply lucas_primality 16516893739069 (2 : ZMod 16516893739069)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (47, 1), (79, 1), (163, 1), (557, 1), (1361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (47, 1), (79, 1), (163, 1), (557, 1), (1361, 1)] : List FactorBlock).map factorBlockValue).prod) = 16516893739069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_47
      · exact prime_fiftyOneAW_79
      · exact prime_fiftyOneAW_163
      · exact prime_fiftyOneAW_557
      · exact prime_fiftyOneAW_1361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16516893739069) ^ 8258446869534 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16516893739069) ^ 5505631246356 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16516893739069) ^ 351423271044 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16516893739069) ^ 209074604292 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16516893739069) ^ 101330636436 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16516893739069) ^ 29653310124 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16516893739069) ^ 12135851388 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_18076669791347 : Nat.Prime 18076669791347 := by
  apply lucas_primality 18076669791347 (2 : ZMod 18076669791347)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (31, 1), (5653, 1), (3033883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (31, 1), (5653, 1), (3033883, 1)] : List FactorBlock).map factorBlockValue).prod) = 18076669791347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_31
      · exact prime_fiftyOneAW_5653
      · exact prime_fiftyOneAW_3033883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18076669791347) ^ 9038334895673 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18076669791347) ^ 1063333517138 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18076669791347) ^ 583118380366 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18076669791347) ^ 3197712682 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18076669791347) ^ 5958262 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_18107153021773 : Nat.Prime 18107153021773 := by
  apply lucas_primality 18107153021773 (2 : ZMod 18107153021773)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (89, 1), (28547, 1), (197969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (89, 1), (28547, 1), (197969, 1)] : List FactorBlock).map factorBlockValue).prod) = 18107153021773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_89
      · exact prime_fiftyOneAW_28547
      · exact prime_fiftyOneAW_197969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18107153021773) ^ 9053576510886 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18107153021773) ^ 6035717673924 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18107153021773) ^ 203451157548 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18107153021773) ^ 634292676 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18107153021773) ^ 91464588 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_24966515977631 : Nat.Prime 24966515977631 := by
  apply lucas_primality 24966515977631 (7 : ZMod 24966515977631)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (367, 1), (6802865389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (367, 1), (6802865389, 1)] : List FactorBlock).map factorBlockValue).prod) = 24966515977631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_367
      · exact prime_fiftyOneAW_6802865389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 24966515977631) ^ 12483257988815 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 24966515977631) ^ 4993303195526 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 24966515977631) ^ 68028653890 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 24966515977631) ^ 3670 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_29116518036253 : Nat.Prime 29116518036253 := by
  apply lucas_primality 29116518036253 (2 : ZMod 29116518036253)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2029, 1), (3187, 1), (375227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2029, 1), (3187, 1), (375227, 1)] : List FactorBlock).map factorBlockValue).prod) = 29116518036253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_2029
      · exact prime_fiftyOneAW_3187
      · exact prime_fiftyOneAW_375227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29116518036253) ^ 14558259018126 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 29116518036253) ^ 9705506012084 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 29116518036253) ^ 14350181388 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 29116518036253) ^ 9136026996 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 29116518036253) ^ 77597076 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_31347428822419 : Nat.Prime 31347428822419 := by
  apply lucas_primality 31347428822419 (3 : ZMod 31347428822419)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1069, 1), (5743, 1), (851009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1069, 1), (5743, 1), (851009, 1)] : List FactorBlock).map factorBlockValue).prod) = 31347428822419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_1069
      · exact prime_fiftyOneAW_5743
      · exact prime_fiftyOneAW_851009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 31347428822419) ^ 15673714411209 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 31347428822419) ^ 10449142940806 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 31347428822419) ^ 29324068122 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 31347428822419) ^ 5458371726 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 31347428822419) ^ 36835602 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_35324456077943 : Nat.Prime 35324456077943 := by
  apply lucas_primality 35324456077943 (5 : ZMod 35324456077943)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (430786049731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (430786049731, 1)] : List FactorBlock).map factorBlockValue).prod) = 35324456077943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_41
      · exact prime_fiftyOneAW_430786049731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 35324456077943) ^ 17662228038971 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 35324456077943) ^ 861572099462 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 35324456077943) ^ 82 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_42621930118723 : Nat.Prime 42621930118723 := by
  apply lucas_primality 42621930118723 (2 : ZMod 42621930118723)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (799361, 1), (8886667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (799361, 1), (8886667, 1)] : List FactorBlock).map factorBlockValue).prod) = 42621930118723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_799361
      · exact prime_fiftyOneAW_8886667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 42621930118723) ^ 21310965059361 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 42621930118723) ^ 14207310039574 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 42621930118723) ^ 53320002 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 42621930118723) ^ 4796166 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_49175923453403 : Nat.Prime 49175923453403 := by
  apply lucas_primality 49175923453403 (2 : ZMod 49175923453403)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (307, 1), (80091080543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (307, 1), (80091080543, 1)] : List FactorBlock).map factorBlockValue).prod) = 49175923453403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_307
      · exact prime_fiftyOneAW_80091080543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 49175923453403) ^ 24587961726701 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 49175923453403) ^ 160182161086 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 49175923453403) ^ 614 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_51072712509703 : Nat.Prime 51072712509703 := by
  apply lucas_primality 51072712509703 (3 : ZMod 51072712509703)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (654778365509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (654778365509, 1)] : List FactorBlock).map factorBlockValue).prod) = 51072712509703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_654778365509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 51072712509703) ^ 25536356254851 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 51072712509703) ^ 17024237503234 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 51072712509703) ^ 3928670193054 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 51072712509703) ^ 78 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_53667885591017 : Nat.Prime 53667885591017 := by
  apply lucas_primality 53667885591017 (3 : ZMod 53667885591017)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (6708485698877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (6708485698877, 1)] : List FactorBlock).map factorBlockValue).prod) = 53667885591017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_6708485698877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 53667885591017) ^ 26833942795508 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 53667885591017) ^ 8 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_60843886065191 : Nat.Prime 60843886065191 := by
  apply lucas_primality 60843886065191 (11 : ZMod 60843886065191)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (401, 1), (15173038919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (401, 1), (15173038919, 1)] : List FactorBlock).map factorBlockValue).prod) = 60843886065191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_401
      · exact prime_fiftyOneAW_15173038919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 60843886065191) ^ 30421943032595 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 60843886065191) ^ 12168777213038 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 60843886065191) ^ 151730389190 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 60843886065191) ^ 4010 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_64611077040737 : Nat.Prime 64611077040737 := by
  apply lucas_primality 64611077040737 (5 : ZMod 64611077040737)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (1181, 1), (89981557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (1181, 1), (89981557, 1)] : List FactorBlock).map factorBlockValue).prod) = 64611077040737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_1181
      · exact prime_fiftyOneAW_89981557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 64611077040737) ^ 32305538520368 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 64611077040737) ^ 3400583002144 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 64611077040737) ^ 54708786656 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 64611077040737) ^ 718048 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_66451830061937 : Nat.Prime 66451830061937 := by
  apply lucas_primality 66451830061937 (3 : ZMod 66451830061937)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (572791, 1), (659171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (572791, 1), (659171, 1)] : List FactorBlock).map factorBlockValue).prod) = 66451830061937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_572791
      · exact prime_fiftyOneAW_659171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 66451830061937) ^ 33225915030968 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 66451830061937) ^ 6041075460176 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 66451830061937) ^ 116014096 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 66451830061937) ^ 100811216 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_74212747541399 : Nat.Prime 74212747541399 := by
  apply lucas_primality 74212747541399 (11 : ZMod 74212747541399)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (251, 1), (883, 1), (167422603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (251, 1), (883, 1), (167422603, 1)] : List FactorBlock).map factorBlockValue).prod) = 74212747541399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_251
      · exact prime_fiftyOneAW_883
      · exact prime_fiftyOneAW_167422603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 74212747541399) ^ 37106373770699 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 74212747541399) ^ 295668316898 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 74212747541399) ^ 84046146706 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 74212747541399) ^ 443266 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_106619097506671 : Nat.Prime 106619097506671 := by
  apply lucas_primality 106619097506671 (12 : ZMod 106619097506671)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (37, 1), (199, 1), (7661581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (37, 1), (199, 1), (7661581, 1)] : List FactorBlock).map factorBlockValue).prod) = 106619097506671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_37
      · exact prime_fiftyOneAW_199
      · exact prime_fiftyOneAW_7661581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 106619097506671) ^ 53309548753335 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 35539699168890 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 21323819501334 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 15231299643810 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 2881597229910 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 535774359330 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 13916070 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_129876803368223 : Nat.Prime 129876803368223 := by
  apply lucas_primality 129876803368223 (5 : ZMod 129876803368223)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (7529, 1), (109178521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (7529, 1), (109178521, 1)] : List FactorBlock).map factorBlockValue).prod) = 129876803368223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_79
      · exact prime_fiftyOneAW_7529
      · exact prime_fiftyOneAW_109178521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 129876803368223) ^ 64938401684111 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 129876803368223) ^ 1644010169218 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 129876803368223) ^ 17250206318 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 129876803368223) ^ 1189582 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_179195277083321 : Nat.Prime 179195277083321 := by
  apply lucas_primality 179195277083321 (3 : ZMod 179195277083321)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (17, 2), (15501321547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (17, 2), (15501321547, 1)] : List FactorBlock).map factorBlockValue).prod) = 179195277083321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_15501321547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 179195277083321) ^ 89597638541660 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 179195277083321) ^ 35839055416664 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 179195277083321) ^ 10540898651960 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 179195277083321) ^ 11560 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_196227824530999 : Nat.Prime 196227824530999 := by
  apply lucas_primality 196227824530999 (6 : ZMod 196227824530999)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (23, 1), (37, 1), (3083, 1), (958877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (23, 1), (37, 1), (3083, 1), (958877, 1)] : List FactorBlock).map factorBlockValue).prod) = 196227824530999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_37
      · exact prime_fiftyOneAW_3083
      · exact prime_fiftyOneAW_958877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 196227824530999) ^ 98113912265499 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 196227824530999) ^ 65409274843666 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 196227824530999) ^ 15094448040846 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 196227824530999) ^ 8531644544826 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 196227824530999) ^ 5303454717054 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 196227824530999) ^ 63648337506 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 196227824530999) ^ 204643374 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_199732127821049 : Nat.Prime 199732127821049 := by
  apply lucas_primality 199732127821049 (3 : ZMod 199732127821049)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (24966515977631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (24966515977631, 1)] : List FactorBlock).map factorBlockValue).prod) = 199732127821049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_24966515977631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 199732127821049) ^ 99866063910524 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 199732127821049) ^ 8 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_204290850038813 : Nat.Prime 204290850038813 := by
  apply lucas_primality 204290850038813 (2 : ZMod 204290850038813)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (51072712509703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (51072712509703, 1)] : List FactorBlock).map factorBlockValue).prod) = 204290850038813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_51072712509703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 204290850038813) ^ 102145425019406 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 204290850038813) ^ 4 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_227264556532219 : Nat.Prime 227264556532219 := by
  apply lucas_primality 227264556532219 (10 : ZMod 227264556532219)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149, 1), (4241, 1), (59941267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149, 1), (4241, 1), (59941267, 1)] : List FactorBlock).map factorBlockValue).prod) = 227264556532219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_149
      · exact prime_fiftyOneAW_4241
      · exact prime_fiftyOneAW_59941267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 227264556532219) ^ 113632278266109 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 227264556532219) ^ 75754852177406 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 227264556532219) ^ 1525265480082 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 227264556532219) ^ 53587492698 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 227264556532219) ^ 3791454 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_228014296889441 : Nat.Prime 228014296889441 := by
  apply lucas_primality 228014296889441 (3 : ZMod 228014296889441)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (149, 1), (9564358091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (149, 1), (9564358091, 1)] : List FactorBlock).map factorBlockValue).prod) = 228014296889441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_149
      · exact prime_fiftyOneAW_9564358091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 228014296889441) ^ 114007148444720 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 228014296889441) ^ 45602859377888 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 228014296889441) ^ 1530297294560 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 228014296889441) ^ 23840 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_318122846667881 : Nat.Prime 318122846667881 := by
  apply lucas_primality 318122846667881 (7 : ZMod 318122846667881)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7953071166697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7953071166697, 1)] : List FactorBlock).map factorBlockValue).prod) = 318122846667881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7953071166697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 318122846667881) ^ 159061423333940 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 318122846667881) ^ 63624569333576 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 318122846667881) ^ 40 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_456113802567517 : Nat.Prime 456113802567517 := by
  apply lucas_primality 456113802567517 (2 : ZMod 456113802567517)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (107, 1), (55103, 1), (6446633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (107, 1), (55103, 1), (6446633, 1)] : List FactorBlock).map factorBlockValue).prod) = 456113802567517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_107
      · exact prime_fiftyOneAW_55103
      · exact prime_fiftyOneAW_6446633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 456113802567517) ^ 228056901283758 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 456113802567517) ^ 152037934189172 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 456113802567517) ^ 4262745818388 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 456113802567517) ^ 8277476772 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 456113802567517) ^ 70752252 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_468249070338449 : Nat.Prime 468249070338449 := by
  apply lucas_primality 468249070338449 (3 : ZMod 468249070338449)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (347, 1), (12048401357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (347, 1), (12048401357, 1)] : List FactorBlock).map factorBlockValue).prod) = 468249070338449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_347
      · exact prime_fiftyOneAW_12048401357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 468249070338449) ^ 234124535169224 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 468249070338449) ^ 66892724334064 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 468249070338449) ^ 1349420951984 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 468249070338449) ^ 38864 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_649574319111587 : Nat.Prime 649574319111587 := by
  apply lucas_primality 649574319111587 (5 : ZMod 649574319111587)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (72869, 1), (405194327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (72869, 1), (405194327, 1)] : List FactorBlock).map factorBlockValue).prod) = 649574319111587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_72869
      · exact prime_fiftyOneAW_405194327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 649574319111587) ^ 324787159555793 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 649574319111587) ^ 59052210828326 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 649574319111587) ^ 8914275194 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 649574319111587) ^ 1603118 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_754643424782869 : Nat.Prime 754643424782869 := by
  apply lucas_primality 754643424782869 (7 : ZMod 754643424782869)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (853, 1), (3880233977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (853, 1), (3880233977, 1)] : List FactorBlock).map factorBlockValue).prod) = 754643424782869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_853
      · exact prime_fiftyOneAW_3880233977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 754643424782869) ^ 377321712391434 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 754643424782869) ^ 251547808260956 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 754643424782869) ^ 39718074988572 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 754643424782869) ^ 884693346756 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 754643424782869) ^ 194484 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_5030435608906837 : Nat.Prime 5030435608906837 := by
  apply lucas_primality 5030435608906837 (2 : ZMod 5030435608906837)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (229, 1), (1830580643707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (229, 1), (1830580643707, 1)] : List FactorBlock).map factorBlockValue).prod) = 5030435608906837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_229
      · exact prime_fiftyOneAW_1830580643707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5030435608906837) ^ 2515217804453418 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5030435608906837) ^ 1676811869635612 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5030435608906837) ^ 21966967724484 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5030435608906837) ^ 2748 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_5484537522705289 : Nat.Prime 5484537522705289 := by
  apply lucas_primality 5484537522705289 (14 : ZMod 5484537522705289)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (8134051, 1), (28094537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (8134051, 1), (28094537, 1)] : List FactorBlock).map factorBlockValue).prod) = 5484537522705289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_8134051
      · exact prime_fiftyOneAW_28094537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 5484537522705289) ^ 2742268761352644 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (14 : ZMod 5484537522705289) ^ 1828179174235096 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (14 : ZMod 5484537522705289) ^ 674268888 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (14 : ZMod 5484537522705289) ^ 195217224 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_8404644125874427 : Nat.Prime 8404644125874427 := by
  apply lucas_primality 8404644125874427 (2 : ZMod 8404644125874427)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (257, 1), (3559, 1), (1531464617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (257, 1), (3559, 1), (1531464617, 1)] : List FactorBlock).map factorBlockValue).prod) = 8404644125874427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_257
      · exact prime_fiftyOneAW_3559
      · exact prime_fiftyOneAW_1531464617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8404644125874427) ^ 4202322062937213 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8404644125874427) ^ 2801548041958142 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8404644125874427) ^ 32702895431418 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8404644125874427) ^ 2361518439414 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8404644125874427) ^ 5487978 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_10108067756202877 : Nat.Prime 10108067756202877 := by
  apply lucas_primality 10108067756202877 (6 : ZMod 10108067756202877)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (3436841, 1), (7906163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (3436841, 1), (7906163, 1)] : List FactorBlock).map factorBlockValue).prod) = 10108067756202877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_31
      · exact prime_fiftyOneAW_3436841
      · exact prime_fiftyOneAW_7906163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10108067756202877) ^ 5054033878101438 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 10108067756202877) ^ 3369355918734292 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 10108067756202877) ^ 326066701812996 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 10108067756202877) ^ 2941092636 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 10108067756202877) ^ 1278504852 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_10967628279619079 : Nat.Prime 10967628279619079 := by
  apply lucas_primality 10967628279619079 (19 : ZMod 10967628279619079)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 2), (2371, 1), (15583, 1), (411143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 2), (2371, 1), (15583, 1), (411143, 1)] : List FactorBlock).map factorBlockValue).prod) = 10967628279619079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_2371
      · exact prime_fiftyOneAW_15583
      · exact prime_fiftyOneAW_411143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 10967628279619079) ^ 5483814139809539 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 10967628279619079) ^ 577243593664162 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 10967628279619079) ^ 4625739468418 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 10967628279619079) ^ 703820078266 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 10967628279619079) ^ 26675945546 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_11655978276633277 : Nat.Prime 11655978276633277 := by
  apply lucas_primality 11655978276633277 (2 : ZMod 11655978276633277)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod) = 11655978276633277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_47
      · exact prime_fiftyOneAW_81047
      · exact prime_fiftyOneAW_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11655978276633277) ^ 5827989138316638 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 3885326092211092 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 685645780978428 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 247999537800708 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 143817516708 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 777078636 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_12698245342134139 : Nat.Prime 12698245342134139 := by
  apply lucas_primality 12698245342134139 (2 : ZMod 12698245342134139)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (233, 1), (23549, 1), (12442349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (233, 1), (23549, 1), (12442349, 1)] : List FactorBlock).map factorBlockValue).prod) = 12698245342134139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_31
      · exact prime_fiftyOneAW_233
      · exact prime_fiftyOneAW_23549
      · exact prime_fiftyOneAW_12442349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12698245342134139) ^ 6349122671067069 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12698245342134139) ^ 4232748447378046 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12698245342134139) ^ 409620817488198 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12698245342134139) ^ 54498907047786 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12698245342134139) ^ 539226520962 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12698245342134139) ^ 1020566562 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_23207078630506919 : Nat.Prime 23207078630506919 := by
  apply lucas_primality 23207078630506919 (11 : ZMod 23207078630506919)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (3691, 1), (64157931401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (3691, 1), (64157931401, 1)] : List FactorBlock).map factorBlockValue).prod) = 23207078630506919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_3691
      · exact prime_fiftyOneAW_64157931401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 23207078630506919) ^ 11603539315253459 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 23207078630506919) ^ 3315296947215274 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 23207078630506919) ^ 6287477277298 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 23207078630506919) ^ 361718 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_28805192514861487 : Nat.Prime 28805192514861487 := by
  apply lucas_primality 28805192514861487 (6 : ZMod 28805192514861487)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (5475539, 1), (23696867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (5475539, 1), (23696867, 1)] : List FactorBlock).map factorBlockValue).prod) = 28805192514861487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_37
      · exact prime_fiftyOneAW_5475539
      · exact prime_fiftyOneAW_23696867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 28805192514861487) ^ 14402596257430743 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 28805192514861487) ^ 9601730838287162 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 28805192514861487) ^ 778518716617878 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 28805192514861487) ^ 5260704474 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 28805192514861487) ^ 1215569658 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_35051778283529219 : Nat.Prime 35051778283529219 := by
  apply lucas_primality 35051778283529219 (2 : ZMod 35051778283529219)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 2), (20509, 1), (2367164141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 2), (20509, 1), (2367164141, 1)] : List FactorBlock).map factorBlockValue).prod) = 35051778283529219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_20509
      · exact prime_fiftyOneAW_2367164141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35051778283529219) ^ 17525889141764609 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35051778283529219) ^ 1844830435975222 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35051778283529219) ^ 1709092509802 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35051778283529219) ^ 14807498 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_48948381560159777 : Nat.Prime 48948381560159777 := by
  apply lucas_primality 48948381560159777 (3 : ZMod 48948381560159777)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (347759, 1), (4398554527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (347759, 1), (4398554527, 1)] : List FactorBlock).map factorBlockValue).prod) = 48948381560159777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_347759
      · exact prime_fiftyOneAW_4398554527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 48948381560159777) ^ 24474190780079888 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 48948381560159777) ^ 140753744864 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 48948381560159777) ^ 11128288 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_69508094572326691 : Nat.Prime 69508094572326691 := by
  apply lucas_primality 69508094572326691 (2 : ZMod 69508094572326691)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (23, 1), (29, 1), (53, 1), (797, 1), (1009, 1), (3881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (23, 1), (29, 1), (53, 1), (797, 1), (1009, 1), (3881, 1)] : List FactorBlock).map factorBlockValue).prod) = 69508094572326691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_53
      · exact prime_fiftyOneAW_797
      · exact prime_fiftyOneAW_1009
      · exact prime_fiftyOneAW_3881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 69508094572326691) ^ 34754047286163345 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 69508094572326691) ^ 23169364857442230 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 69508094572326691) ^ 13901618914465338 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 69508094572326691) ^ 9929727796046670 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 69508094572326691) ^ 3022091068362030 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 69508094572326691) ^ 2396830847321610 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 69508094572326691) ^ 1311473482496730 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 69508094572326691) ^ 87212163829770 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 69508094572326691) ^ 68888101657410 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 69508094572326691) ^ 17909841425490 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_94982709331929571 : Nat.Prime 94982709331929571 := by
  apply lucas_primality 94982709331929571 (2 : ZMod 94982709331929571)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (101, 1), (31347428822419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (101, 1), (31347428822419, 1)] : List FactorBlock).map factorBlockValue).prod) = 94982709331929571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_101
      · exact prime_fiftyOneAW_31347428822419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 94982709331929571) ^ 47491354665964785 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 94982709331929571) ^ 31660903110643190 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 94982709331929571) ^ 18996541866385914 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 94982709331929571) ^ 940422864672570 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 94982709331929571) ^ 3030 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_102223266935858869 : Nat.Prime 102223266935858869 := by
  apply lucas_primality 102223266935858869 (2 : ZMod 102223266935858869)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (61, 1), (627481, 1), (11713441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (61, 1), (627481, 1), (11713441, 1)] : List FactorBlock).map factorBlockValue).prod) = 102223266935858869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_61
      · exact prime_fiftyOneAW_627481
      · exact prime_fiftyOneAW_11713441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 102223266935858869) ^ 51111633467929434 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 102223266935858869) ^ 34074422311952956 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 102223266935858869) ^ 5380171943992572 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 102223266935858869) ^ 1675791261243588 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 102223266935858869) ^ 162910537428 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 102223266935858869) ^ 8727005748 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_109273444804007593 : Nat.Prime 109273444804007593 := by
  apply lucas_primality 109273444804007593 (5 : ZMod 109273444804007593)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (59, 1), (2661052133353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (59, 1), (2661052133353, 1)] : List FactorBlock).map factorBlockValue).prod) = 109273444804007593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_59
      · exact prime_fiftyOneAW_2661052133353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 109273444804007593) ^ 54636722402003796 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 109273444804007593) ^ 36424481601335864 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 109273444804007593) ^ 3768049820827848 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 109273444804007593) ^ 1852092284813688 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 109273444804007593) ^ 41064 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_113814267595358257 : Nat.Prime 113814267595358257 := by
  apply lucas_primality 113814267595358257 (5 : ZMod 113814267595358257)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (43, 1), (6126952389931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (43, 1), (6126952389931, 1)] : List FactorBlock).map factorBlockValue).prod) = 113814267595358257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_43
      · exact prime_fiftyOneAW_6126952389931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 113814267595358257) ^ 56907133797679128 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 113814267595358257) ^ 37938089198452752 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 113814267595358257) ^ 2646843432450192 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 113814267595358257) ^ 18576 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_116559782766332771 : Nat.Prime 116559782766332771 := by
  apply lucas_primality 116559782766332771 (2 : ZMod 116559782766332771)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod) = 116559782766332771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116559782766332771) ^ 58279891383166385 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 23311956553266554 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 10 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_158688716705120461 : Nat.Prime 158688716705120461 := by
  apply lucas_primality 158688716705120461 (7 : ZMod 158688716705120461)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (97, 1), (4919, 1), (5543017387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (97, 1), (4919, 1), (5543017387, 1)] : List FactorBlock).map factorBlockValue).prod) = 158688716705120461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_97
      · exact prime_fiftyOneAW_4919
      · exact prime_fiftyOneAW_5543017387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 158688716705120461) ^ 79344358352560230 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 158688716705120461) ^ 52896238901706820 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 158688716705120461) ^ 31737743341024092 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 158688716705120461) ^ 1635966151599180 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 158688716705120461) ^ 32260361192340 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 158688716705120461) ^ 28628580 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_256585995159334433 : Nat.Prime 256585995159334433 := by
  apply lucas_primality 256585995159334433 (3 : ZMod 256585995159334433)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (70633193, 1), (113520457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (70633193, 1), (113520457, 1)] : List FactorBlock).map factorBlockValue).prod) = 256585995159334433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_70633193
      · exact prime_fiftyOneAW_113520457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 256585995159334433) ^ 128292997579667216 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 256585995159334433) ^ 3632654624 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 256585995159334433) ^ 2260262176 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_414773857789524941 : Nat.Prime 414773857789524941 := by
  apply lucas_primality 414773857789524941 (2 : ZMod 414773857789524941)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (61, 1), (6889997, 1), (7049113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (61, 1), (6889997, 1), (7049113, 1)] : List FactorBlock).map factorBlockValue).prod) = 414773857789524941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_61
      · exact prime_fiftyOneAW_6889997
      · exact prime_fiftyOneAW_7049113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 414773857789524941) ^ 207386928894762470 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 414773857789524941) ^ 82954771557904988 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 414773857789524941) ^ 59253408255646420 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 414773857789524941) ^ 6799571439172540 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 414773857789524941) ^ 60199425020 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 414773857789524941) ^ 58840574380 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_460640387744001319 : Nat.Prime 460640387744001319 := by
  apply lucas_primality 460640387744001319 (6 : ZMod 460640387744001319)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (10967628279619079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (10967628279619079, 1)] : List FactorBlock).map factorBlockValue).prod) = 460640387744001319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_10967628279619079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 460640387744001319) ^ 230320193872000659 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 460640387744001319) ^ 153546795914667106 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 460640387744001319) ^ 65805769677714474 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (6 : ZMod 460640387744001319) ^ 42 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_504051854825488309 : Nat.Prime 504051854825488309 := by
  apply lucas_primality 504051854825488309 (13 : ZMod 504051854825488309)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (277, 1), (49417, 1), (133416637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (277, 1), (49417, 1), (133416637, 1)] : List FactorBlock).map factorBlockValue).prod) = 504051854825488309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_277
      · exact prime_fiftyOneAW_49417
      · exact prime_fiftyOneAW_133416637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 504051854825488309) ^ 252025927412744154 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (13 : ZMod 504051854825488309) ^ 168017284941829436 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (13 : ZMod 504051854825488309) ^ 21915298035890796 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (13 : ZMod 504051854825488309) ^ 1819681786373604 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (13 : ZMod 504051854825488309) ^ 10199968731924 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (13 : ZMod 504051854825488309) ^ 3778028484 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_61717
      · exact prime_fiftyOneAW_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_682885605572149543 : Nat.Prime 682885605572149543 := by
  apply lucas_primality 682885605572149543 (3 : ZMod 682885605572149543)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113814267595358257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113814267595358257, 1)] : List FactorBlock).map factorBlockValue).prod) = 682885605572149543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_113814267595358257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 682885605572149543) ^ 341442802786074771 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 682885605572149543) ^ 227628535190716514 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 682885605572149543) ^ 6 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_875215878218305237 : Nat.Prime 875215878218305237 := by
  apply lucas_primality 875215878218305237 (2 : ZMod 875215878218305237)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (151, 1), (53667885591017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (151, 1), (53667885591017, 1)] : List FactorBlock).map factorBlockValue).prod) = 875215878218305237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_151
      · exact prime_fiftyOneAW_53667885591017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 875215878218305237) ^ 437607939109152618 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 875215878218305237) ^ 291738626072768412 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 875215878218305237) ^ 5796131643829836 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 875215878218305237) ^ 16308 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_881025965873339851 : Nat.Prime 881025965873339851 := by
  apply lucas_primality 881025965873339851 (2 : ZMod 881025965873339851)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (53, 1), (2621, 1), (14093968741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (53, 1), (2621, 1), (14093968741, 1)] : List FactorBlock).map factorBlockValue).prod) = 881025965873339851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_53
      · exact prime_fiftyOneAW_2621
      · exact prime_fiftyOneAW_14093968741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 881025965873339851) ^ 440512982936669925 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 881025965873339851) ^ 293675321957779950 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 881025965873339851) ^ 176205193174667970 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 881025965873339851) ^ 16623131431572450 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 881025965873339851) ^ 336141154472850 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 881025965873339851) ^ 62510850 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1806210658167367321 : Nat.Prime 1806210658167367321 := by
  apply lucas_primality 1806210658167367321 (19 : ZMod 1806210658167367321)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (11, 1), (456113802567517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (11, 1), (456113802567517, 1)] : List FactorBlock).map factorBlockValue).prod) = 1806210658167367321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_456113802567517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1806210658167367321) ^ 903105329083683660 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 1806210658167367321) ^ 602070219389122440 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 1806210658167367321) ^ 361242131633473464 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 1806210658167367321) ^ 164200968924306120 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (19 : ZMod 1806210658167367321) ^ 3960 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_2502291404603760877 : Nat.Prime 2502291404603760877 := by
  apply lucas_primality 2502291404603760877 (5 : ZMod 2502291404603760877)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (69508094572326691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (69508094572326691, 1)] : List FactorBlock).map factorBlockValue).prod) = 2502291404603760877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_69508094572326691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2502291404603760877) ^ 1251145702301880438 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2502291404603760877) ^ 834097134867920292 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2502291404603760877) ^ 36 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_3379627908495294503 : Nat.Prime 3379627908495294503 := by
  apply lucas_primality 3379627908495294503 (5 : ZMod 3379627908495294503)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7411, 1), (228014296889441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7411, 1), (228014296889441, 1)] : List FactorBlock).map factorBlockValue).prod) = 3379627908495294503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_7411
      · exact prime_fiftyOneAW_228014296889441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3379627908495294503) ^ 1689813954247647251 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3379627908495294503) ^ 456028593778882 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3379627908495294503) ^ 14822 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_5287789172857120001 : Nat.Prime 5287789172857120001 := by
  apply lucas_primality 5287789172857120001 (3 : ZMod 5287789172857120001)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 4), (53, 1), (208333, 1), (2993093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 4), (53, 1), (208333, 1), (2993093, 1)] : List FactorBlock).map factorBlockValue).prod) = 5287789172857120001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_53
      · exact prime_fiftyOneAW_208333
      · exact prime_fiftyOneAW_2993093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5287789172857120001) ^ 2643894586428560000 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5287789172857120001) ^ 1057557834571424000 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5287789172857120001) ^ 99769607035040000 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5287789172857120001) ^ 25381428640000 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5287789172857120001) ^ 1766663840000 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_6533831533403812223 : Nat.Prime 6533831533403812223 := by
  apply lucas_primality 6533831533403812223 (5 : ZMod 6533831533403812223)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2357, 1), (106619097506671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2357, 1), (106619097506671, 1)] : List FactorBlock).map factorBlockValue).prod) = 6533831533403812223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_2357
      · exact prime_fiftyOneAW_106619097506671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6533831533403812223) ^ 3266915766701906111 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 6533831533403812223) ^ 502602425646447094 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 6533831533403812223) ^ 2772096535173446 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 6533831533403812223) ^ 61282 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_7307626741325773553 : Nat.Prime 7307626741325773553 := by
  apply lucas_primality 7307626741325773553 (3 : ZMod 7307626741325773553)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (337, 1), (619, 1), (2189453993149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (337, 1), (619, 1), (2189453993149, 1)] : List FactorBlock).map factorBlockValue).prod) = 7307626741325773553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_337
      · exact prime_fiftyOneAW_619
      · exact prime_fiftyOneAW_2189453993149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7307626741325773553) ^ 3653813370662886776 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7307626741325773553) ^ 21684352348147696 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7307626741325773553) ^ 11805535931059408 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7307626741325773553) ^ 3337648 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_9380849132145063077 : Nat.Prime 9380849132145063077 := by
  apply lucas_primality 9380849132145063077 (2 : ZMod 9380849132145063077)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (347, 1), (6551, 1), (5082168359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (347, 1), (6551, 1), (5082168359, 1)] : List FactorBlock).map factorBlockValue).prod) = 9380849132145063077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_347
      · exact prime_fiftyOneAW_6551
      · exact prime_fiftyOneAW_5082168359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9380849132145063077) ^ 4690424566072531538 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9380849132145063077) ^ 1340121304592151868 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9380849132145063077) ^ 323477556280864244 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9380849132145063077) ^ 27034147354884908 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9380849132145063077) ^ 1431972085505276 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9380849132145063077) ^ 1845835964 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_12748558038206052259 : Nat.Prime 12748558038206052259 := by
  apply lucas_primality 12748558038206052259 (3 : ZMod 12748558038206052259)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (17, 1), (251149, 1), (3385416493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (17, 1), (251149, 1), (3385416493, 1)] : List FactorBlock).map factorBlockValue).prod) = 12748558038206052259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_251149
      · exact prime_fiftyOneAW_3385416493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12748558038206052259) ^ 6374279019103026129 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12748558038206052259) ^ 4249519346068684086 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12748558038206052259) ^ 1821222576886578894 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12748558038206052259) ^ 749915178718003074 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12748558038206052259) ^ 50760934896042 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12748558038206052259) ^ 3765728106 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_16175045358502498537 : Nat.Prime 16175045358502498537 := by
  apply lucas_primality 16175045358502498537 (10 : ZMod 16175045358502498537)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1231, 1), (182887, 1), (2993597287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1231, 1), (182887, 1), (2993597287, 1)] : List FactorBlock).map factorBlockValue).prod) = 16175045358502498537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_1231
      · exact prime_fiftyOneAW_182887
      · exact prime_fiftyOneAW_2993597287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 16175045358502498537) ^ 8087522679251249268 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 16175045358502498537) ^ 5391681786167499512 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 16175045358502498537) ^ 13139760648661656 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 16175045358502498537) ^ 88442838247128 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 16175045358502498537) ^ 5403213528 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_17906527684083735577 : Nat.Prime 17906527684083735577 := by
  apply lucas_primality 17906527684083735577 (7 : ZMod 17906527684083735577)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (103, 1), (127, 1), (1728403954313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (103, 1), (127, 1), (1728403954313, 1)] : List FactorBlock).map factorBlockValue).prod) = 17906527684083735577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_103
      · exact prime_fiftyOneAW_127
      · exact prime_fiftyOneAW_1728403954313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 17906527684083735577) ^ 8953263842041867788 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 17906527684083735577) ^ 5968842561361245192 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 17906527684083735577) ^ 1627866153098521416 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 17906527684083735577) ^ 173849783340618792 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 17906527684083735577) ^ 140996280977037288 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 17906527684083735577) ^ 10360152 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_31255574362747278433 : Nat.Prime 31255574362747278433 := by
  apply lucas_primality 31255574362747278433 (5 : ZMod 31255574362747278433)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (31, 1), (83, 1), (18076669791347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (31, 1), (83, 1), (18076669791347, 1)] : List FactorBlock).map factorBlockValue).prod) = 31255574362747278433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_31
      · exact prime_fiftyOneAW_83
      · exact prime_fiftyOneAW_18076669791347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 31255574362747278433) ^ 15627787181373639216 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 31255574362747278433) ^ 10418524787582426144 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 31255574362747278433) ^ 4465082051821039776 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 31255574362747278433) ^ 1008244334282170272 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 31255574362747278433) ^ 376573185093340704 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 31255574362747278433) ^ 1729056 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_43105346097783439507 : Nat.Prime 43105346097783439507 := by
  apply lucas_primality 43105346097783439507 (2 : ZMod 43105346097783439507)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (3013783, 1), (23601876497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (3013783, 1), (23601876497, 1)] : List FactorBlock).map factorBlockValue).prod) = 43105346097783439507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_101
      · exact prime_fiftyOneAW_3013783
      · exact prime_fiftyOneAW_23601876497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43105346097783439507) ^ 21552673048891719753 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 43105346097783439507) ^ 14368448699261146502 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 43105346097783439507) ^ 426785604928548906 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 43105346097783439507) ^ 14302737157182 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 43105346097783439507) ^ 1826352498 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_47004755940671233151 : Nat.Prime 47004755940671233151 := by
  apply lucas_primality 47004755940671233151 (17 : ZMod 47004755940671233151)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (3779, 1), (6287, 1), (39568669331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (3779, 1), (6287, 1), (39568669331, 1)] : List FactorBlock).map factorBlockValue).prod) = 47004755940671233151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_3779
      · exact prime_fiftyOneAW_6287
      · exact prime_fiftyOneAW_39568669331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 47004755940671233151) ^ 23502377970335616575 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (17 : ZMod 47004755940671233151) ^ 9400951188134246630 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (17 : ZMod 47004755940671233151) ^ 12438411204199850 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (17 : ZMod 47004755940671233151) ^ 7476500070092450 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (17 : ZMod 47004755940671233151) ^ 1187928650 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_85992210770920657639 : Nat.Prime 85992210770920657639 := by
  apply lucas_primality 85992210770920657639 (3 : ZMod 85992210770920657639)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (163, 1), (677, 1), (129876803368223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (163, 1), (677, 1), (129876803368223, 1)] : List FactorBlock).map factorBlockValue).prod) = 85992210770920657639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_163
      · exact prime_fiftyOneAW_677
      · exact prime_fiftyOneAW_129876803368223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 85992210770920657639) ^ 42996105385460328819 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 85992210770920657639) ^ 28664070256973552546 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 85992210770920657639) ^ 527559575281721826 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 85992210770920657639) ^ 127019513694122094 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 85992210770920657639) ^ 662106 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_117003213792656501449 : Nat.Prime 117003213792656501449 := by
  apply lucas_primality 117003213792656501449 (17 : ZMod 117003213792656501449)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (256585995159334433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (256585995159334433, 1)] : List FactorBlock).map factorBlockValue).prod) = 117003213792656501449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_256585995159334433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 117003213792656501449) ^ 58501606896328250724 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (17 : ZMod 117003213792656501449) ^ 39001071264218833816 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (17 : ZMod 117003213792656501449) ^ 6158063883824026392 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (17 : ZMod 117003213792656501449) ^ 456 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_169345120476587740441 : Nat.Prime 169345120476587740441 := by
  apply lucas_primality 169345120476587740441 (37 : ZMod 169345120476587740441)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 2), (157477, 1), (182885059769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 2), (157477, 1), (182885059769, 1)] : List FactorBlock).map factorBlockValue).prod) = 169345120476587740441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_157477
      · exact prime_fiftyOneAW_182885059769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 169345120476587740441) ^ 84672560238293870220 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (37 : ZMod 169345120476587740441) ^ 56448373492195913480 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (37 : ZMod 169345120476587740441) ^ 33869024095317548088 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (37 : ZMod 169345120476587740441) ^ 24192160068083962920 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (37 : ZMod 169345120476587740441) ^ 1075364151441720 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (37 : ZMod 169345120476587740441) ^ 925964760 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_179342389870853805599 : Nat.Prime 179342389870853805599 := by
  apply lucas_primality 179342389870853805599 (11 : ZMod 179342389870853805599)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (136601, 1), (7908989265053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (136601, 1), (7908989265053, 1)] : List FactorBlock).map factorBlockValue).prod) = 179342389870853805599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_83
      · exact prime_fiftyOneAW_136601
      · exact prime_fiftyOneAW_7908989265053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 179342389870853805599) ^ 89671194935426902799 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 179342389870853805599) ^ 2160751685191009706 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 179342389870853805599) ^ 1312892217998798 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 179342389870853805599) ^ 22675766 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_443831096543292924709 : Nat.Prime 443831096543292924709 := by
  apply lucas_primality 443831096543292924709 (2 : ZMod 443831096543292924709)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (8511353, 1), (395043748273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (8511353, 1), (395043748273, 1)] : List FactorBlock).map factorBlockValue).prod) = 443831096543292924709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_8511353
      · exact prime_fiftyOneAW_395043748273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 443831096543292924709) ^ 221915548271646462354 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 443831096543292924709) ^ 147943698847764308236 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 443831096543292924709) ^ 40348281503935720428 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 443831096543292924709) ^ 52145774772036 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 443831096543292924709) ^ 1123498596 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_982717613585267701301 : Nat.Prime 982717613585267701301 := by
  apply lucas_primality 982717613585267701301 (2 : ZMod 982717613585267701301)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (256258957, 1), (38348615209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (256258957, 1), (38348615209, 1)] : List FactorBlock).map factorBlockValue).prod) = 982717613585267701301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_256258957
      · exact prime_fiftyOneAW_38348615209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 982717613585267701301) ^ 491358806792633850650 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 982717613585267701301) ^ 196543522717053540260 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 982717613585267701301) ^ 3834861520900 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 982717613585267701301) ^ 25625895700 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_107
      · exact prime_fiftyOneAW_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_6634598692464619845923 : Nat.Prime 6634598692464619845923 := by
  apply lucas_primality 6634598692464619845923 (2 : ZMod 6634598692464619845923)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (1087, 1), (206489, 1), (202458184399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (1087, 1), (206489, 1), (202458184399, 1)] : List FactorBlock).map factorBlockValue).prod) = 6634598692464619845923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_73
      · exact prime_fiftyOneAW_1087
      · exact prime_fiftyOneAW_206489
      · exact prime_fiftyOneAW_202458184399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6634598692464619845923) ^ 3317299346232309922961 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6634598692464619845923) ^ 90884913595405751314 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6634598692464619845923) ^ 6103586653601306206 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6634598692464619845923) ^ 32130518780490098 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6634598692464619845923) ^ 32770217278 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_15900384904147437529243 : Nat.Prime 15900384904147437529243 := by
  apply lucas_primality 15900384904147437529243 (2 : ZMod 15900384904147437529243)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (523, 1), (460640387744001319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (523, 1), (460640387744001319, 1)] : List FactorBlock).map factorBlockValue).prod) = 15900384904147437529243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_523
      · exact prime_fiftyOneAW_460640387744001319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15900384904147437529243) ^ 7950192452073718764621 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15900384904147437529243) ^ 5300128301382479176414 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15900384904147437529243) ^ 1445489536740676139022 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15900384904147437529243) ^ 30402265591104087054 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15900384904147437529243) ^ 34518 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_23784406505979643974407 : Nat.Prime 23784406505979643974407 := by
  apply lucas_primality 23784406505979643974407 (5 : ZMod 23784406505979643974407)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (47004755940671233151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (47004755940671233151, 1)] : List FactorBlock).map factorBlockValue).prod) = 23784406505979643974407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_47004755940671233151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 23784406505979643974407) ^ 11892203252989821987203 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 23784406505979643974407) ^ 2162218773270876724946 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 23784406505979643974407) ^ 1034104630694767129322 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 23784406505979643974407) ^ 506 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_45008547834389284082893 : Nat.Prime 45008547834389284082893 := by
  apply lucas_primality 45008547834389284082893 (2 : ZMod 45008547834389284082893)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (743, 1), (123846461, 1), (40760672467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (743, 1), (123846461, 1), (40760672467, 1)] : List FactorBlock).map factorBlockValue).prod) = 45008547834389284082893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_743
      · exact prime_fiftyOneAW_123846461
      · exact prime_fiftyOneAW_40760672467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45008547834389284082893) ^ 22504273917194642041446 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45008547834389284082893) ^ 15002849278129761360964 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45008547834389284082893) ^ 60576780396217071444 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45008547834389284082893) ^ 363422155715772 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45008547834389284082893) ^ 1104215046276 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_48277002932255897663783 : Nat.Prime 48277002932255897663783 := by
  apply lucas_primality 48277002932255897663783 (5 : ZMod 48277002932255897663783)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83047, 1), (13251499, 1), (21934177247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83047, 1), (13251499, 1), (21934177247, 1)] : List FactorBlock).map factorBlockValue).prod) = 48277002932255897663783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_83047
      · exact prime_fiftyOneAW_13251499
      · exact prime_fiftyOneAW_21934177247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 48277002932255897663783) ^ 24138501466127948831891 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 48277002932255897663783) ^ 581321455708886506 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 48277002932255897663783) ^ 3643135235663218 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 48277002932255897663783) ^ 2200994474906 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_50117498837774501089349 : Nat.Prime 50117498837774501089349 := by
  apply lucas_primality 50117498837774501089349 (2 : ZMod 50117498837774501089349)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (42571, 1), (79192871, 1), (530922851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (42571, 1), (79192871, 1), (530922851, 1)] : List FactorBlock).map factorBlockValue).prod) = 50117498837774501089349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_42571
      · exact prime_fiftyOneAW_79192871
      · exact prime_fiftyOneAW_530922851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50117498837774501089349) ^ 25058749418887250544674 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 50117498837774501089349) ^ 7159642691110643012764 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 50117498837774501089349) ^ 1177268535805466188 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 50117498837774501089349) ^ 632853667317788 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 50117498837774501089349) ^ 94396951917548 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_449330137038854874752809 : Nat.Prime 449330137038854874752809 := by
  apply lucas_primality 449330137038854874752809 (7 : ZMod 449330137038854874752809)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (599, 1), (31255574362747278433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (599, 1), (31255574362747278433, 1)] : List FactorBlock).map factorBlockValue).prod) = 449330137038854874752809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_599
      · exact prime_fiftyOneAW_31255574362747278433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 449330137038854874752809) ^ 224665068519427437376404 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 449330137038854874752809) ^ 149776712346284958250936 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 449330137038854874752809) ^ 750133784705934682392 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (7 : ZMod 449330137038854874752809) ^ 14376 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_524665521738604754904017 : Nat.Prime 524665521738604754904017 := by
  apply lucas_primality 524665521738604754904017 (3 : ZMod 524665521738604754904017)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (206641, 1), (158688716705120461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (206641, 1), (158688716705120461, 1)] : List FactorBlock).map factorBlockValue).prod) = 524665521738604754904017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_206641
      · exact prime_fiftyOneAW_158688716705120461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 524665521738604754904017) ^ 262332760869302377452008 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 524665521738604754904017) ^ 2539019467281927376 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 524665521738604754904017) ^ 3306256 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_642262580839837405657003 : Nat.Prime 642262580839837405657003 := by
  apply lucas_primality 642262580839837405657003 (3 : ZMod 642262580839837405657003)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (23, 1), (823, 1), (1303, 1), (4915219, 1), (51939467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (23, 1), (823, 1), (1303, 1), (4915219, 1), (51939467, 1)] : List FactorBlock).map factorBlockValue).prod) = 642262580839837405657003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_823
      · exact prime_fiftyOneAW_1303
      · exact prime_fiftyOneAW_4915219
      · exact prime_fiftyOneAW_51939467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 642262580839837405657003) ^ 321131290419918702828501 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 642262580839837405657003) ^ 214087526946612468552334 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 642262580839837405657003) ^ 37780151814108082685706 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 642262580839837405657003) ^ 27924460036514669811174 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 642262580839837405657003) ^ 780391957278052740774 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 642262580839837405657003) ^ 492910652985293480934 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 642262580839837405657003) ^ 130668151478059758 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 642262580839837405657003) ^ 12365598223020606 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1719587357096849636181823 : Nat.Prime 1719587357096849636181823 := by
  apply lucas_primality 1719587357096849636181823 (5 : ZMod 1719587357096849636181823)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (6827, 1), (95430239, 1), (146634385643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (6827, 1), (95430239, 1), (146634385643, 1)] : List FactorBlock).map factorBlockValue).prod) = 1719587357096849636181823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_6827
      · exact prime_fiftyOneAW_95430239
      · exact prime_fiftyOneAW_146634385643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1719587357096849636181823) ^ 859793678548424818090911 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1719587357096849636181823) ^ 573195785698949878727274 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1719587357096849636181823) ^ 251880380415533856186 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1719587357096849636181823) ^ 18019313114125698 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1719587357096849636181823) ^ 11727040349754 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_2377493438320410695283287 : Nat.Prime 2377493438320410695283287 := by
  apply lucas_primality 2377493438320410695283287 (5 : ZMod 2377493438320410695283287)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (397, 1), (187751, 1), (179195277083321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (397, 1), (187751, 1), (179195277083321, 1)] : List FactorBlock).map factorBlockValue).prod) = 2377493438320410695283287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_89
      · exact prime_fiftyOneAW_397
      · exact prime_fiftyOneAW_187751
      · exact prime_fiftyOneAW_179195277083321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2377493438320410695283287) ^ 1188746719160205347641643 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2377493438320410695283287) ^ 26713409419330457250374 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2377493438320410695283287) ^ 5988648459245366990638 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2377493438320410695283287) ^ 12663013450369961786 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2377493438320410695283287) ^ 13267612166 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_3053251523660316773500073 : Nat.Prime 3053251523660316773500073 := by
  apply lucas_primality 3053251523660316773500073 (3 : ZMod 3053251523660316773500073)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (12373, 1), (477409, 1), (64611077040737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (12373, 1), (477409, 1), (64611077040737, 1)] : List FactorBlock).map factorBlockValue).prod) = 3053251523660316773500073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_12373
      · exact prime_fiftyOneAW_477409
      · exact prime_fiftyOneAW_64611077040737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3053251523660316773500073) ^ 1526625761830158386750036 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3053251523660316773500073) ^ 246767277431529683464 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3053251523660316773500073) ^ 6395462849800311208 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3053251523660316773500073) ^ 47255852456 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_6246955148077490224106863 : Nat.Prime 6246955148077490224106863 := by
  apply lucas_primality 6246955148077490224106863 (3 : ZMod 6246955148077490224106863)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (19, 1), (12773071, 1), (204290850038813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (19, 1), (12773071, 1), (204290850038813, 1)] : List FactorBlock).map factorBlockValue).prod) = 6246955148077490224106863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_12773071
      · exact prime_fiftyOneAW_204290850038813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6246955148077490224106863) ^ 3123477574038745112053431 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6246955148077490224106863) ^ 2082318382692496741368954 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6246955148077490224106863) ^ 892422164011070032015266 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6246955148077490224106863) ^ 328787113056710011795098 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6246955148077490224106863) ^ 489072294992918322 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6246955148077490224106863) ^ 30578731974 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_9205436807518158113447243 : Nat.Prime 9205436807518158113447243 := by
  apply lucas_primality 9205436807518158113447243 (5 : ZMod 9205436807518158113447243)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (401867, 1), (881025965873339851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (401867, 1), (881025965873339851, 1)] : List FactorBlock).map factorBlockValue).prod) = 9205436807518158113447243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_401867
      · exact prime_fiftyOneAW_881025965873339851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9205436807518158113447243) ^ 4602718403759079056723621 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 9205436807518158113447243) ^ 708110523655242931803634 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 9205436807518158113447243) ^ 22906675112706836126 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 9205436807518158113447243) ^ 10448542 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_14291446098422359716302309 : Nat.Prime 14291446098422359716302309 := by
  apply lucas_primality 14291446098422359716302309 (2 : ZMod 14291446098422359716302309)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (61, 1), (199, 1), (155976109, 1), (111000841031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (61, 1), (199, 1), (155976109, 1), (111000841031, 1)] : List FactorBlock).map factorBlockValue).prod) = 14291446098422359716302309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_61
      · exact prime_fiftyOneAW_199
      · exact prime_fiftyOneAW_155976109
      · exact prime_fiftyOneAW_111000841031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14291446098422359716302309) ^ 7145723049211179858151154 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14291446098422359716302309) ^ 840673299907197630370724 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14291446098422359716302309) ^ 234286001613481306824628 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14291446098422359716302309) ^ 71816312052373666916092 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14291446098422359716302309) ^ 91625866230721012 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14291446098422359716302309) ^ 128750791126268 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_15230010378692582885344643 : Nat.Prime 15230010378692582885344643 := by
  apply lucas_primality 15230010378692582885344643 (2 : ZMod 15230010378692582885344643)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (479, 1), (619, 1), (983, 1), (173293, 1), (2844681403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (479, 1), (619, 1), (983, 1), (173293, 1), (2844681403, 1)] : List FactorBlock).map factorBlockValue).prod) = 15230010378692582885344643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_53
      · exact prime_fiftyOneAW_479
      · exact prime_fiftyOneAW_619
      · exact prime_fiftyOneAW_983
      · exact prime_fiftyOneAW_173293
      · exact prime_fiftyOneAW_2844681403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15230010378692582885344643) ^ 7615005189346291442672321 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15230010378692582885344643) ^ 287358686390426092176314 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15230010378692582885344643) ^ 31795428765537751326398 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15230010378692582885344643) ^ 24604217089971862496518 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15230010378692582885344643) ^ 15493398147194896119374 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15230010378692582885344643) ^ 87885894864146750794 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15230010378692582885344643) ^ 5353854516935014 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_31453109592719841232696631 : Nat.Prime 31453109592719841232696631 := by
  apply lucas_primality 31453109592719841232696631 (11 : ZMod 31453109592719841232696631)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (449330137038854874752809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (449330137038854874752809, 1)] : List FactorBlock).map factorBlockValue).prod) = 31453109592719841232696631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_449330137038854874752809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 31453109592719841232696631) ^ 15726554796359920616348315 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 31453109592719841232696631) ^ 6290621918543968246539326 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 31453109592719841232696631) ^ 4493301370388548747528090 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (11 : ZMod 31453109592719841232696631) ^ 70 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_51622954699695150379348837 : Nat.Prime 51622954699695150379348837 := by
  apply lucas_primality 51622954699695150379348837 (2 : ZMod 51622954699695150379348837)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (251, 1), (17958571, 1), (318122846667881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (251, 1), (17958571, 1), (318122846667881, 1)] : List FactorBlock).map factorBlockValue).prod) = 51622954699695150379348837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_251
      · exact prime_fiftyOneAW_17958571
      · exact prime_fiftyOneAW_318122846667881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51622954699695150379348837) ^ 25811477349847575189674418 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 51622954699695150379348837) ^ 17207651566565050126449612 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 51622954699695150379348837) ^ 205669142229861156889836 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 51622954699695150379348837) ^ 2874558042490972716 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 51622954699695150379348837) ^ 162273647556 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_648339904185418662828811201 : Nat.Prime 648339904185418662828811201 := by
  apply lucas_primality 648339904185418662828811201 (73 : ZMod 648339904185418662828811201)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 648339904185418662828811201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_37
      · exact prime_fiftyOneAW_41
      · exact prime_fiftyOneAW_43
      · exact prime_fiftyOneAW_47
      · exact prime_fiftyOneAW_53
      · exact prime_fiftyOneAW_59
      · exact prime_fiftyOneAW_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 648339904185418662828811201) ^ 324169952092709331414405600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 216113301395139554276270400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 129667980837083732565762240 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 92619986312202666118401600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 58939991289583514802619200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 49872300321955281756062400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 38137641422671686048753600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 34123152851864140148884800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 28188691486322550557774400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 22356548420186850442372800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 17522700113119423319697600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 15813168394766308849483200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 15077672190358573554158400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 13794466046498269421889600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 12232828380856955902430400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 10988811935346079030996800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 10628523019433092833259200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1076707340879355993626418601 : Nat.Prime 1076707340879355993626418601 := by
  apply lucas_primality 1076707340879355993626418601 (103 : ZMod 1076707340879355993626418601)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 2), (7, 1), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 2), (7, 1), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1076707340879355993626418601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_31
      · exact prime_fiftyOneAW_37
      · exact prime_fiftyOneAW_41
      · exact prime_fiftyOneAW_43
      · exact prime_fiftyOneAW_47
      · exact prime_fiftyOneAW_53
      · exact prime_fiftyOneAW_59
      · exact prime_fiftyOneAW_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 1076707340879355993626418601) ^ 538353670439677996813209300 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 1076707340879355993626418601) ^ 358902446959785331208806200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 1076707340879355993626418601) ^ 215341468175871198725283720 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 1076707340879355993626418601) ^ 153815334411336570518059800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 1076707340879355993626418601) ^ 97882485534486908511492600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 1076707340879355993626418601) ^ 82823641606104307202032200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 1076707340879355993626418601) ^ 63335725934079764330965800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 1076707340879355993626418601) ^ 56668807414702947032969400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 1076707340879355993626418601) ^ 46813362646928521462018200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 1076707340879355993626418601) ^ 37127839340667448056083400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 1076707340879355993626418601) ^ 34732494867075999794400600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 1076707340879355993626418601) ^ 29100198402144756584497800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 1076707340879355993626418601) ^ 26261154655594048625034600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 1076707340879355993626418601) ^ 25039705601845488223870200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 1076707340879355993626418601) ^ 22908666827220340289923800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 1076707340879355993626418601) ^ 20315232846780301766536200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 1076707340879355993626418601) ^ 18249276964056881247905400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 1076707340879355993626418601) ^ 17650940014415672026662600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1370354797482816719160896401 : Nat.Prime 1370354797482816719160896401 := by
  apply lucas_primality 1370354797482816719160896401 (83 : ZMod 1370354797482816719160896401)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (5, 2), (7, 2), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (5, 2), (7, 2), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1370354797482816719160896401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_31
      · exact prime_fiftyOneAW_37
      · exact prime_fiftyOneAW_41
      · exact prime_fiftyOneAW_43
      · exact prime_fiftyOneAW_47
      · exact prime_fiftyOneAW_53
      · exact prime_fiftyOneAW_59
      · exact prime_fiftyOneAW_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 1370354797482816719160896401) ^ 685177398741408359580448200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1370354797482816719160896401) ^ 456784932494272239720298800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1370354797482816719160896401) ^ 274070959496563343832179280 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1370354797482816719160896401) ^ 195764971068973817022985200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1370354797482816719160896401) ^ 105411907498678209166222800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1370354797482816719160896401) ^ 80609105734283336421229200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1370354797482816719160896401) ^ 72123936709621932587415600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1370354797482816719160896401) ^ 59580643368818118224386800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1370354797482816719160896401) ^ 47253613706304024798651600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1370354797482816719160896401) ^ 44204993467187636101964400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1370354797482816719160896401) ^ 37036616148184235652997200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1370354797482816719160896401) ^ 33423287743483334613680400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1370354797482816719160896401) ^ 31868716220530621375834800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1370354797482816719160896401) ^ 29156485052825887641721200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1370354797482816719160896401) ^ 25855750895902202248318800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1370354797482816719160896401) ^ 23226352499708757951879600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1370354797482816719160896401) ^ 22464832745619946215752400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1402223513703347340536731201 : Nat.Prime 1402223513703347340536731201 := by
  apply lucas_primality 1402223513703347340536731201 (83 : ZMod 1402223513703347340536731201)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1402223513703347340536731201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_31
      · exact prime_fiftyOneAW_37
      · exact prime_fiftyOneAW_41
      · exact prime_fiftyOneAW_47
      · exact prime_fiftyOneAW_53
      · exact prime_fiftyOneAW_59
      · exact prime_fiftyOneAW_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 1402223513703347340536731201) ^ 701111756851673670268365600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1402223513703347340536731201) ^ 467407837901115780178910400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1402223513703347340536731201) ^ 280444702740669468107346240 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1402223513703347340536731201) ^ 200317644814763905790961600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1402223513703347340536731201) ^ 127474864882122485503339200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1402223513703347340536731201) ^ 107863347207949795425902400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1402223513703347340536731201) ^ 82483736100196902384513600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1402223513703347340536731201) ^ 73801237563334070554564800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1402223513703347340536731201) ^ 60966239726232493066814400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1402223513703347340536731201) ^ 48352534955287839328852800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1402223513703347340536731201) ^ 45233016571075720662475200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1402223513703347340536731201) ^ 37897932802793171365857600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1402223513703347340536731201) ^ 34200573504959691232603200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1402223513703347340536731201) ^ 29834542844752071075249600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1402223513703347340536731201) ^ 26457047428365044161070400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1402223513703347340536731201) ^ 23766500232260124415876800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (83 : ZMod 1402223513703347340536731201) ^ 22987270716448317057979200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1546041309980613734437934401 : Nat.Prime 1546041309980613734437934401 := by
  apply lucas_primality 1546041309980613734437934401 (26 : ZMod 1546041309980613734437934401)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1546041309980613734437934401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_31
      · exact prime_fiftyOneAW_37
      · exact prime_fiftyOneAW_41
      · exact prime_fiftyOneAW_43
      · exact prime_fiftyOneAW_47
      · exact prime_fiftyOneAW_53
      · exact prime_fiftyOneAW_59
      · exact prime_fiftyOneAW_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 1546041309980613734437934401) ^ 773020654990306867218967200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 515347103326871244812644800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 309208261996122746887586880 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 220863044282944819205419200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 140549209998237612221630400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 90943606469447866731643200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 81370595262137564970417600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 67219187390461466714692800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 53311769309676335670273600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 49872300321955281756062400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 41784900269746317146971200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 37708324633673505717998400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 35954449069316598475300800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 32894495957034334775275200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 29170590754351202536564800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 26204089999671419227761600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 25344939507878913679310400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_1674878085812331545641095601 : Nat.Prime 1674878085812331545641095601 := by
  apply lucas_primality 1674878085812331545641095601 (107 : ZMod 1674878085812331545641095601)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1674878085812331545641095601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_31
      · exact prime_fiftyOneAW_37
      · exact prime_fiftyOneAW_41
      · exact prime_fiftyOneAW_43
      · exact prime_fiftyOneAW_47
      · exact prime_fiftyOneAW_53
      · exact prime_fiftyOneAW_59
      · exact prime_fiftyOneAW_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 1674878085812331545641095601) ^ 837439042906165772820547800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 558292695270777181880365200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 334975617162466309128219120 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 239268297973190220805870800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 152261644164757413240099600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 128836775831717811203161200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 98522240341901855625946800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 88151478200649028717952400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 72820786339666588940917200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 57754416752149363642796400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 54028325348784888569067600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 45266975292225176909218800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 40850685019812964527831600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 38950653158426315014909200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 35635703953453862673214800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 31601473317213802747945200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 28387764166310704163408400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 27457017800202156485919600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_2153414681758711987252837201 : Nat.Prime 2153414681758711987252837201 := by
  apply lucas_primality 2153414681758711987252837201 (73 : ZMod 2153414681758711987252837201)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (5, 2), (7, 1), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (5, 2), (7, 1), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2153414681758711987252837201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_31
      · exact prime_fiftyOneAW_37
      · exact prime_fiftyOneAW_41
      · exact prime_fiftyOneAW_43
      · exact prime_fiftyOneAW_47
      · exact prime_fiftyOneAW_53
      · exact prime_fiftyOneAW_59
      · exact prime_fiftyOneAW_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 2153414681758711987252837201) ^ 1076707340879355993626418600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 2153414681758711987252837201) ^ 717804893919570662417612400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 2153414681758711987252837201) ^ 430682936351742397450567440 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 2153414681758711987252837201) ^ 307630668822673141036119600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 2153414681758711987252837201) ^ 195764971068973817022985200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 2153414681758711987252837201) ^ 165647283212208614404064400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 2153414681758711987252837201) ^ 126671451868159528661931600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 2153414681758711987252837201) ^ 113337614829405894065938800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 2153414681758711987252837201) ^ 93626725293857042924036400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 2153414681758711987252837201) ^ 74255678681334896112166800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 2153414681758711987252837201) ^ 69464989734151999588801200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 2153414681758711987252837201) ^ 58200396804289513168995600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 2153414681758711987252837201) ^ 52522309311188097250069200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 2153414681758711987252837201) ^ 50079411203690976447740400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 2153414681758711987252837201) ^ 45817333654440680579847600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 2153414681758711987252837201) ^ 40630465693560603533072400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 2153414681758711987252837201) ^ 36498553928113762495810800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (73 : ZMod 2153414681758711987252837201) ^ 35301880028831344053325200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_10049268514873989273846573601 : Nat.Prime 10049268514873989273846573601 := by
  apply lucas_primality 10049268514873989273846573601 (103 : ZMod 10049268514873989273846573601)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 10049268514873989273846573601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_5
      · exact prime_fiftyOneAW_7
      · exact prime_fiftyOneAW_11
      · exact prime_fiftyOneAW_13
      · exact prime_fiftyOneAW_17
      · exact prime_fiftyOneAW_19
      · exact prime_fiftyOneAW_23
      · exact prime_fiftyOneAW_29
      · exact prime_fiftyOneAW_31
      · exact prime_fiftyOneAW_37
      · exact prime_fiftyOneAW_41
      · exact prime_fiftyOneAW_43
      · exact prime_fiftyOneAW_47
      · exact prime_fiftyOneAW_53
      · exact prime_fiftyOneAW_59
      · exact prime_fiftyOneAW_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 10049268514873989273846573601) ^ 5024634257436994636923286800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 3349756171624663091282191200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 2009853702974797854769314720 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 1435609787839141324835224800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 913569864988544479440597600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 773020654990306867218967200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 591133442051411133755680800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 528908869203894172307714400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 436924718037999533645503200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 346526500512896181856778400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 324169952092709331414405600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 271601851753351061455312800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 245104110118877787166989600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 233703918950557890089455200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 213814223720723176039288800 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 189608839903282816487671200 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 170326584997864224980450400 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 164742106801212938915517600 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_60295611089243935643079441683 : Nat.Prime 60295611089243935643079441683 := by
  apply lucas_primality 60295611089243935643079441683 (2 : ZMod 60295611089243935643079441683)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (503, 1), (881, 1), (5197, 1), (250298611, 1), (1275606721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (503, 1), (881, 1), (5197, 1), (250298611, 1), (1275606721, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_41
      · exact prime_fiftyOneAW_503
      · exact prime_fiftyOneAW_881
      · exact prime_fiftyOneAW_5197
      · exact prime_fiftyOneAW_250298611
      · exact prime_fiftyOneAW_1275606721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60295611089243935643079441683) ^ 30147805544621967821539720841 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 60295611089243935643079441683) ^ 1470624660713266723001937602 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 60295611089243935643079441683) ^ 119871990237065478415664894 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 60295611089243935643079441683) ^ 68439967184158837279318322 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 60295611089243935643079441683) ^ 11602003288290155020796506 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 60295611089243935643079441683) ^ 240894709117039149862 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (2 : ZMod 60295611089243935643079441683) ^ 47268182345398551442 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem prime_fiftyOneAW_60295611089243935643079441697 : Nat.Prime 60295611089243935643079441697 := by
  apply lucas_primality 60295611089243935643079441697 (5 : ZMod 60295611089243935643079441697)
  · rw [← fiftyOneAWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7303909, 1), (85992210770920657639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7303909, 1), (85992210770920657639, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyOneAW_2
      · exact prime_fiftyOneAW_3
      · exact prime_fiftyOneAW_7303909
      · exact prime_fiftyOneAW_85992210770920657639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 60295611089243935643079441697) ^ 30147805544621967821539720848 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 60295611089243935643079441697) ^ 20098537029747978547693147232 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 60295611089243935643079441697) ^ 8255252234008383133344 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide
    · change (5 : ZMod 60295611089243935643079441697) ^ 701175264 ≠ 1
      rw [← fiftyOneAWFastPow_eq_pow]
      decide

private theorem phi_fiftyOneAW_60295611089243935643079441600 : Nat.totient 60295611089243935643079441600 = 7934139791427392608665600000 := by
  rw [← show ((([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441600 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_3, prime_fiftyOneAW_5, prime_fiftyOneAW_7, prime_fiftyOneAW_11, prime_fiftyOneAW_13, prime_fiftyOneAW_17, prime_fiftyOneAW_19, prime_fiftyOneAW_23, prime_fiftyOneAW_29, prime_fiftyOneAW_31, prime_fiftyOneAW_37, prime_fiftyOneAW_41, prime_fiftyOneAW_43, prime_fiftyOneAW_47, prime_fiftyOneAW_53, prime_fiftyOneAW_59, prime_fiftyOneAW_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441601 : Nat.totient 60295611089243935643079441601 = 59960985860924397498216441600 := by
  rw [← show ((([(271, 1), (541, 1), (79579, 1), (177493, 1), (29116518036253, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441601 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_271, prime_fiftyOneAW_541, prime_fiftyOneAW_79579, prime_fiftyOneAW_177493, prime_fiftyOneAW_29116518036253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441602 : Nat.totient 60295611089243935643079441602 = 30089849577295102589474579088 := by
  rw [← show ((([(2, 1), (683, 1), (2179, 1), (89134547, 1), (227264556532219, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441602 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_683, prime_fiftyOneAW_2179, prime_fiftyOneAW_89134547, prime_fiftyOneAW_227264556532219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441603 : Nat.totient 60295611089243935643079441603 = 40179389430869923424791192320 := by
  rw [← show ((([(3, 1), (2273, 1), (1052072531, 1), (8404644125874427, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441603 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_3, prime_fiftyOneAW_2273, prime_fiftyOneAW_1052072531, prime_fiftyOneAW_8404644125874427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441604 : Nat.totient 60295611089243935643079441604 = 30141699041574647187992710784 := by
  rw [← show ((([(2, 2), (4937, 1), (3053251523660316773500073, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441604 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_4937, prime_fiftyOneAW_3053251523660316773500073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441605 : Nat.totient 60295611089243935643079441605 = 47738858183447767565284972800 := by
  rw [← show ((([(5, 1), (101, 1), (2383, 1), (255334613, 1), (196227824530999, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441605 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_5, prime_fiftyOneAW_101, prime_fiftyOneAW_2383, prime_fiftyOneAW_255334613, prime_fiftyOneAW_196227824530999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441606 : Nat.totient 60295611089243935643079441606 = 20098537029747978547693147200 := by
  rw [← show ((([(2, 1), (3, 1), (10049268514873989273846573601, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441606 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_3, prime_fiftyOneAW_10049268514873989273846573601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441607 : Nat.totient 60295611089243935643079441607 = 51667687401579165229896371352 := by
  rw [← show ((([(7, 1), (3623, 1), (2377493438320410695283287, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441607 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_7, prime_fiftyOneAW_3623, prime_fiftyOneAW_2377493438320410695283287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441608 : Nat.totient 60295611089243935643079441608 = 30021663994800250738483771008 := by
  rw [← show ((([(2, 3), (239, 1), (288591263, 1), (109273444804007593, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441608 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_239, prime_fiftyOneAW_288591263, prime_fiftyOneAW_109273444804007593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441609 : Nat.totient 60295611089243935643079441609 = 40184502975031532510712533760 := by
  rw [← show ((([(3, 2), (3863, 1), (19891, 1), (299027, 1), (3960137, 1), (73627703, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441609 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_3, prime_fiftyOneAW_3863, prime_fiftyOneAW_19891, prime_fiftyOneAW_299027, prime_fiftyOneAW_3960137, prime_fiftyOneAW_73627703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441610 : Nat.totient 60295611089243935643079441610 = 24093707461159962964394387520 := by
  rw [← show ((([(2, 1), (5, 1), (983, 1), (14788387, 1), (414773857789524941, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441610 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_5, prime_fiftyOneAW_983, prime_fiftyOneAW_14788387, prime_fiftyOneAW_414773857789524941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441611 : Nat.totient 60295611089243935643079441611 = 54192463655841809240666243520 := by
  rw [← show ((([(11, 1), (89, 1), (9283, 1), (6634598692464619845923, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441611 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_11, prime_fiftyOneAW_89, prime_fiftyOneAW_9283, prime_fiftyOneAW_6634598692464619845923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441612 : Nat.totient 60295611089243935643079441612 = 20098537029339085283335598016 := by
  rw [← show ((([(2, 2), (3, 1), (49153528429, 1), (102223266935858869, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441612 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_3, prime_fiftyOneAW_49153528429, prime_fiftyOneAW_102223266935858869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441613 : Nat.totient 60295611089243935643079441613 = 55654817793577577081428409856 := by
  rw [← show ((([(13, 1), (20947, 1), (4523579, 1), (48948381560159777, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441613 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_13, prime_fiftyOneAW_20947, prime_fiftyOneAW_4523579, prime_fiftyOneAW_48948381560159777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441614 : Nat.totient 60295611089243935643079441614 = 25840976180534647318982676600 := by
  rw [← show ((([(2, 1), (7, 1), (45343298731, 1), (94982709331929571, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441614 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_7, prime_fiftyOneAW_45343298731, prime_fiftyOneAW_94982709331929571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441615 : Nat.totient 60295611089243935643079441615 = 31750599371990475642326728704 := by
  rw [← show ((([(3, 1), (5, 1), (79, 1), (52142977, 1), (111306893, 1), (8766968939, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441615 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_3, prime_fiftyOneAW_5, prime_fiftyOneAW_79, prime_fiftyOneAW_52142977, prime_fiftyOneAW_111306893, prime_fiftyOneAW_8766968939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441616 : Nat.totient 60295611089243935643079441616 = 29734821907024406618504929536 := by
  rw [← show ((([(2, 4), (73, 1), (51622954699695150379348837, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441616 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_73, prime_fiftyOneAW_51622954699695150379348837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441617 : Nat.totient 60295611089243935643079441617 = 56748810435070511829419617600 := by
  rw [← show ((([(17, 1), (30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441617 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_17, prime_fiftyOneAW_30429025931, prime_fiftyOneAW_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441618 : Nat.totient 60295611089243935643079441618 = 20052737314351811313966626112 := by
  rw [← show ((([(2, 1), (3, 2), (439, 1), (1167833, 1), (6533831533403812223, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441618 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_3, prime_fiftyOneAW_439, prime_fiftyOneAW_1167833, prime_fiftyOneAW_6533831533403812223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441619 : Nat.totient 60295611089243935643079441619 = 57122154825808402030316515200 := by
  rw [← show ((([(19, 1), (18739561, 1), (169345120476587740441, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441619 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_19, prime_fiftyOneAW_18739561, prime_fiftyOneAW_169345120476587740441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441620 : Nat.totient 60295611089243935643079441620 = 24118244435695855647255245312 := by
  rw [← show ((([(2, 2), (5, 1), (15094119245369, 1), (199732127821049, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441620 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_5, prime_fiftyOneAW_15094119245369, prime_fiftyOneAW_199732127821049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441621 : Nat.totient 60295611089243935643079441621 = 34453557224512898958089904384 := by
  rw [← show ((([(3, 1), (7, 1), (54833, 1), (76679, 1), (682885605572149543, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441621 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_3, prime_fiftyOneAW_7, prime_fiftyOneAW_54833, prime_fiftyOneAW_76679, prime_fiftyOneAW_682885605572149543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441622 : Nat.totient 60295611089243935643079441622 = 27335392763005223409923719200 := by
  rw [← show ((([(2, 1), (11, 1), (383, 1), (341659, 1), (425911, 1), (49175923453403, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441622 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_11, prime_fiftyOneAW_383, prime_fiftyOneAW_341659, prime_fiftyOneAW_425911, prime_fiftyOneAW_49175923453403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441623 : Nat.totient 60295611089243935643079441623 = 57674061832698324288632773944 := by
  rw [← show ((([(23, 1), (60817243, 1), (43105346097783439507, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441623 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_23, prime_fiftyOneAW_60817243, prime_fiftyOneAW_43105346097783439507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441624 : Nat.totient 60295611089243935643079441624 = 20093832662412838958298316800 := by
  rw [← show ((([(2, 3), (3, 1), (4801, 1), (40163, 1), (1133689, 1), (11492716013243, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441624 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_3, prime_fiftyOneAW_4801, prime_fiftyOneAW_40163, prime_fiftyOneAW_1133689, prime_fiftyOneAW_11492716013243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441625 : Nat.totient 60295611089243935643079441625 = 48228845221318560044551888000 := by
  rw [← show ((([(5, 3), (6311, 1), (117665369, 1), (649574319111587, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441625 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_5, prime_fiftyOneAW_6311, prime_fiftyOneAW_117665369, prime_fiftyOneAW_649574319111587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441626 : Nat.totient 60295611089243935643079441626 = 27506713718084987850557783040 := by
  rw [← show ((([(2, 1), (13, 1), (157, 1), (191, 1), (6090257, 1), (12698245342134139, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441626 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_13, prime_fiftyOneAW_157, prime_fiftyOneAW_191, prime_fiftyOneAW_6090257, prime_fiftyOneAW_12698245342134139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441627 : Nat.totient 60295611089243935643079441627 = 39630918086826999953197753800 := by
  rw [← show ((([(3, 3), (71, 1), (31453109592719841232696631, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441627 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_3, prime_fiftyOneAW_71, prime_fiftyOneAW_31453109592719841232696631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441628 : Nat.totient 60295611089243935643079441628 = 25840976181104543847034046400 := by
  rw [← show ((([(2, 2), (7, 1), (2153414681758711987252837201, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441628 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_7, prime_fiftyOneAW_2153414681758711987252837201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441629 : Nat.totient 60295611089243935643079441629 = 57959911271942541420234044544 := by
  rw [← show ((([(29, 1), (227, 1), (718457, 1), (12748558038206052259, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441629 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_29, prime_fiftyOneAW_227, prime_fiftyOneAW_718457, prime_fiftyOneAW_12748558038206052259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441630 : Nat.totient 60295611089243935643079441630 = 16078639348546335001002046496 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (84503, 1), (23784406505979643974407, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441630 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_3, prime_fiftyOneAW_5, prime_fiftyOneAW_84503, prime_fiftyOneAW_23784406505979643974407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441631 : Nat.totient 60295611089243935643079441631 = 58053639769153514059532444640 := by
  rw [← show ((([(31, 1), (199, 1), (15583, 1), (8451647, 1), (74212747541399, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441631 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_31, prime_fiftyOneAW_199, prime_fiftyOneAW_15583, prime_fiftyOneAW_8451647, prime_fiftyOneAW_74212747541399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441632 : Nat.totient 60295611089243935643079441632 = 30147805504585305335831467392 := by
  rw [← show ((([(2, 5), (753004963, 1), (2502291404603760877, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441632 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_753004963, prime_fiftyOneAW_2502291404603760877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441633 : Nat.totient 60295611089243935643079441633 = 36541829059483134059669871440 := by
  rw [← show ((([(3, 1), (11, 1), (37847, 1), (48277002932255897663783, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441633 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_3, prime_fiftyOneAW_11, prime_fiftyOneAW_37847, prime_fiftyOneAW_48277002932255897663783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441634 : Nat.totient 60295611089243935643079441634 = 28370652939155871076617400320 := by
  rw [← show ((([(2, 1), (17, 1), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441634 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_17, prime_fiftyOneAW_8233, prime_fiftyOneAW_93811, prime_fiftyOneAW_8274073, prime_fiftyOneAW_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441635 : Nat.totient 60295611089243935643079441635 = 41345561868762089030774732928 := by
  rw [← show ((([(5, 1), (7, 1), (1968350653, 1), (875215878218305237, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441635 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_5, prime_fiftyOneAW_7, prime_fiftyOneAW_1968350653, prime_fiftyOneAW_875215878218305237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441636 : Nat.totient 60295611089243935643079441636 = 20098537029747978547693147200 := by
  rw [← show ((([(2, 2), (3, 2), (1674878085812331545641095601, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441636 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_3, prime_fiftyOneAW_1674878085812331545641095601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441637 : Nat.totient 60295611089243935643079441637 = 58117719605090896290475153872 := by
  rw [← show ((([(37, 1), (107, 1), (15230010378692582885344643, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441637 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_37, prime_fiftyOneAW_107, prime_fiftyOneAW_15230010378692582885344643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441638 : Nat.totient 60295611089243935643079441638 = 28558530781955815944215416320 := by
  rw [← show ((([(2, 1), (19, 1), (11213, 1), (28130321, 1), (5030435608906837, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441638 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_19, prime_fiftyOneAW_11213, prime_fiftyOneAW_28130321, prime_fiftyOneAW_5030435608906837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441639 : Nat.totient 60295611089243935643079441639 = 37104991439534729626510425600 := by
  rw [← show ((([(3, 1), (13, 1), (1546041309980613734437934401, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441639 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_3, prime_fiftyOneAW_13, prime_fiftyOneAW_1546041309980613734437934401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441640 : Nat.totient 60295611089243935643079441640 = 24107968234404136858741227072 := by
  rw [← show ((([(2, 3), (5, 1), (2347, 1), (642262580839837405657003, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441640 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_5, prime_fiftyOneAW_2347, prime_fiftyOneAW_642262580839837405657003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441641 : Nat.totient 60295611089243935643079441641 = 58822948057276404630337382400 := by
  rw [← show ((([(41, 1), (28859, 1), (4594920691, 1), (11090280900929, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441641 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_41, prime_fiftyOneAW_28859, prime_fiftyOneAW_4594920691, prime_fiftyOneAW_11090280900929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441642 : Nat.totient 60295611089243935643079441642 = 17225380226836514425896612864 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (8893, 1), (344755493, 1), (468249070338449, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441642 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_3, prime_fiftyOneAW_7, prime_fiftyOneAW_8893, prime_fiftyOneAW_344755493, prime_fiftyOneAW_468249070338449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441643 : Nat.totient 60295611089243935643079441643 = 58893387575540588302542710400 := by
  rw [← show ((([(43, 1), (1402223513703347340536731201, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441643 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_43, prime_fiftyOneAW_1402223513703347340536731201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441644 : Nat.totient 60295611089243935643079441644 = 27407095949656334383217928000 := by
  rw [← show ((([(2, 2), (11, 1), (1370354797482816719160896401, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441644 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_11, prime_fiftyOneAW_1370354797482816719160896401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441645 : Nat.totient 60295611089243935643079441645 = 32085781099187610219624105984 := by
  rw [← show ((([(3, 2), (5, 1), (743, 1), (1123, 1), (88685873, 1), (18107153021773, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441645 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_3, prime_fiftyOneAW_5, prime_fiftyOneAW_743, prime_fiftyOneAW_1123, prime_fiftyOneAW_88685873, prime_fiftyOneAW_18107153021773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441646 : Nat.totient 60295611089243935643079441646 = 28834334071109588164650999360 := by
  rw [← show ((([(2, 1), (23, 1), (10691, 1), (30158010563, 1), (4065433399897, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441646 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_23, prime_fiftyOneAW_10691, prime_fiftyOneAW_30158010563, prime_fiftyOneAW_4065433399897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441647 : Nat.totient 60295611089243935643079441647 = 59012725503681294624256000000 := by
  rw [← show ((([(47, 1), (242612801, 1), (5287789172857120001, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441647 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_47, prime_fiftyOneAW_242612801, prime_fiftyOneAW_5287789172857120001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441648 : Nat.totient 60295611089243935643079441648 = 20087533331840496319801344000 := by
  rw [← show ((([(2, 4), (3, 1), (2693, 1), (5701, 1), (1231261, 1), (66451830061937, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441648 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_3, prime_fiftyOneAW_2693, prime_fiftyOneAW_5701, prime_fiftyOneAW_1231261, prime_fiftyOneAW_66451830061937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441649 : Nat.totient 60295611089243935643079441649 = 51652458404892041489999845632 := by
  rw [← show ((([(7, 3), (1753, 1), (4321049, 1), (23207078630506919, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441649 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_7, prime_fiftyOneAW_1753, prime_fiftyOneAW_4321049, prime_fiftyOneAW_23207078630506919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441650 : Nat.totient 60295611089243935643079441650 = 23934135699547211094962829200 := by
  rw [← show ((([(2, 1), (5, 2), (131, 1), (9205436807518158113447243, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441650 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_5, prime_fiftyOneAW_131, prime_fiftyOneAW_9205436807518158113447243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441651 : Nat.totient 60295611089243935643079441651 = 37457754491305460464031238144 := by
  rw [← show ((([(3, 1), (17, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441651 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_3, prime_fiftyOneAW_17, prime_fiftyOneAW_103, prime_fiftyOneAW_5009, prime_fiftyOneAW_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441652 : Nat.totient 60295611089243935643079441652 = 27828740771573916195888938496 := by
  rw [← show ((([(2, 2), (13, 1), (9910249, 1), (117003213792656501449, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441652 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_13, prime_fiftyOneAW_9910249, prime_fiftyOneAW_117003213792656501449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441653 : Nat.totient 60295611089243935643079441653 = 59144289390981843119201894400 := by
  rw [← show ((([(53, 1), (4831, 1), (44263, 1), (680321, 1), (7820203803977, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441653 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_53, prime_fiftyOneAW_4831, prime_fiftyOneAW_44263, prime_fiftyOneAW_680321, prime_fiftyOneAW_7820203803977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441654 : Nat.totient 60295611089243935643079441654 = 20044747363833510704930801664 := by
  rw [← show ((([(2, 1), (3, 3), (397, 1), (6337, 1), (443831096543292924709, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441654 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_3, prime_fiftyOneAW_397, prime_fiftyOneAW_6337, prime_fiftyOneAW_443831096543292924709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441655 : Nat.totient 60295611089243935643079441655 = 43850717504053969115644757280 := by
  rw [← show ((([(5, 1), (11, 1), (68947, 1), (15900384904147437529243, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441655 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_5, prime_fiftyOneAW_11, prime_fiftyOneAW_68947, prime_fiftyOneAW_15900384904147437529243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441656 : Nat.totient 60295611089243935643079441656 = 25840976181104543847034046400 := by
  rw [← show ((([(2, 3), (7, 1), (1076707340879355993626418601, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441656 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_7, prime_fiftyOneAW_1076707340879355993626418601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441657 : Nat.totient 60295611089243935643079441657 = 37718771040016505677096427520 := by
  rw [← show ((([(3, 1), (19, 1), (109, 1), (2857, 1), (439441, 1), (9978323, 1), (774668639, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441657 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_3, prime_fiftyOneAW_19, prime_fiftyOneAW_109, prime_fiftyOneAW_2857, prime_fiftyOneAW_439441, prime_fiftyOneAW_9978323, prime_fiftyOneAW_774668639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441658 : Nat.totient 60295611089243935643079441658 = 29108225992509380831167468800 := by
  rw [← show ((([(2, 1), (29, 1), (575558281, 1), (1806210658167367321, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441658 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_29, prime_fiftyOneAW_575558281, prime_fiftyOneAW_1806210658167367321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441659 : Nat.totient 60295611089243935643079441659 = 58662582845887407980381808384 := by
  rw [← show ((([(59, 1), (97, 1), (365755759, 1), (28805192514861487, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441659 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_59, prime_fiftyOneAW_97, prime_fiftyOneAW_365755759, prime_fiftyOneAW_28805192514861487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441660 : Nat.totient 60295611089243935643079441660 = 16054573684073352997834137600 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (887, 1), (3637, 1), (11317, 1), (54601, 1), (504121961207, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441660 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_3, prime_fiftyOneAW_5, prime_fiftyOneAW_887, prime_fiftyOneAW_3637, prime_fiftyOneAW_11317, prime_fiftyOneAW_54601, prime_fiftyOneAW_504121961207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441661 : Nat.totient 60295611089243935643079441661 = 58874259481162294358623420800 := by
  rw [← show ((([(61, 1), (137, 1), (118581886303, 1), (60843886065191, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441661 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_61, prime_fiftyOneAW_137, prime_fiftyOneAW_118581886303, prime_fiftyOneAW_60843886065191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441662 : Nat.totient 60295611089243935643079441662 = 28671243636083419273569955200 := by
  rw [← show ((([(2, 1), (31, 1), (67, 1), (419, 1), (3427181, 1), (10108067756202877, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441662 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_31, prime_fiftyOneAW_67, prime_fiftyOneAW_419, prime_fiftyOneAW_3427181, prime_fiftyOneAW_10108067756202877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441663 : Nat.totient 60295611089243935643079441663 = 34454634889993524953972478144 := by
  rw [← show ((([(3, 2), (7, 1), (1898759389, 1), (504051854825488309, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441663 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_3, prime_fiftyOneAW_7, prime_fiftyOneAW_1898759389, prime_fiftyOneAW_504051854825488309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441664 : Nat.totient 60295611089243935643079441664 = 30142044450499165993176440832 := by
  rw [← show ((([(2, 8), (5233, 1), (45008547834389284082893, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441664 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_5233, prime_fiftyOneAW_45008547834389284082893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441665 : Nat.totient 60295611089243935643079441665 = 43792269544456656855863567616 := by
  rw [← show ((([(5, 1), (13, 1), (83, 1), (223, 1), (50117498837774501089349, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441665 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_5, prime_fiftyOneAW_13, prime_fiftyOneAW_83, prime_fiftyOneAW_223, prime_fiftyOneAW_50117498837774501089349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441666 : Nat.totient 60295611089243935643079441666 = 18270813902962957596702321600 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (31319, 1), (111179436971, 1), (262367120149, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441666 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_3, prime_fiftyOneAW_11, prime_fiftyOneAW_31319, prime_fiftyOneAW_111179436971, prime_fiftyOneAW_262367120149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441667 : Nat.totient 60295611089243935643079441667 = 60285844959257084243690325600 := by
  rw [← show ((([(6211, 1), (1034861, 1), (9380849132145063077, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441667 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_6211, prime_fiftyOneAW_1034861, prime_fiftyOneAW_9380849132145063077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441668 : Nat.totient 60295611089243935643079441668 = 28320986566452283220282572800 := by
  rw [← show ((([(2, 2), (17, 1), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441668 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_17, prime_fiftyOneAW_769, prime_fiftyOneAW_2143, prime_fiftyOneAW_8597, prime_fiftyOneAW_9792301, prime_fiftyOneAW_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441669 : Nat.totient 60295611089243935643079441669 = 38449257697570002901343531520 := by
  rw [← show ((([(3, 1), (23, 1), (327263, 1), (21764550497, 1), (122684585791, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441669 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_3, prime_fiftyOneAW_23, prime_fiftyOneAW_327263, prime_fiftyOneAW_21764550497, prime_fiftyOneAW_122684585791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441670 : Nat.totient 60295611089243935643079441670 = 20672780769500593282979739648 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (117872177, 1), (7307626741325773553, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441670 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_5, prime_fiftyOneAW_7, prime_fiftyOneAW_117872177, prime_fiftyOneAW_7307626741325773553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441671 : Nat.totient 60295611089243935643079441671 = 60281319643145513283363135144 := by
  rw [← show ((([(4219, 1), (14291446098422359716302309, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441671 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_4219, prime_fiftyOneAW_14291446098422359716302309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441672 : Nat.totient 60295611089243935643079441672 = 20057266933177654156424771808 := by
  rw [← show ((([(2, 3), (3, 2), (487, 1), (1719587357096849636181823, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441672 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_3, prime_fiftyOneAW_487, prime_fiftyOneAW_1719587357096849636181823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441673 : Nat.totient 60295611089243935643079441673 = 60236439698223398376164675808 := by
  rw [← show ((([(1019, 1), (1688112793, 1), (35051778283529219, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441673 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_1019, prime_fiftyOneAW_1688112793, prime_fiftyOneAW_35051778283529219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441674 : Nat.totient 60295611089243935643079441674 = 29314112030579324865997181952 := by
  rw [← show ((([(2, 1), (37, 1), (1553, 1), (524665521738604754904017, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441674 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_37, prime_fiftyOneAW_1553, prime_fiftyOneAW_524665521738604754904017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441675 : Nat.totient 60295611089243935643079441675 = 31899481471843934642496552960 := by
  rw [← show ((([(3, 1), (5, 2), (197, 1), (337, 1), (16046729, 1), (754643424782869, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441675 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_3, prime_fiftyOneAW_5, prime_fiftyOneAW_197, prime_fiftyOneAW_337, prime_fiftyOneAW_16046729, prime_fiftyOneAW_754643424782869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441676 : Nat.totient 60295611089243935643079441676 = 28336188551679495656548726032 := by
  rw [← show ((([(2, 2), (19, 1), (127, 1), (6246955148077490224106863, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441676 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_19, prime_fiftyOneAW_127, prime_fiftyOneAW_6246955148077490224106863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441677 : Nat.totient 60295611089243935643079441677 = 46983574738330919603716193280 := by
  rw [← show ((([(7, 1), (11, 1), (2584079, 1), (344909167, 1), (878586350657, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441677 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_7, prime_fiftyOneAW_11, prime_fiftyOneAW_2584079, prime_fiftyOneAW_344909167, prime_fiftyOneAW_878586350657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441678 : Nat.totient 60295611089243935643079441678 = 18552491099672826914414254080 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (4930417, 1), (21642461, 1), (7244372988773, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441678 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_3, prime_fiftyOneAW_13, prime_fiftyOneAW_4930417, prime_fiftyOneAW_21642461, prime_fiftyOneAW_7244372988773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441679 : Nat.totient 60295611089243935643079441679 = 59974077892862464935884144640 := by
  rw [← show ((([(257, 1), (691, 1), (61906253, 1), (5484537522705289, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441679 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_257, prime_fiftyOneAW_691, prime_fiftyOneAW_61906253, prime_fiftyOneAW_5484537522705289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441680 : Nat.totient 60295611089243935643079441680 = 24117138396910690462407052800 := by
  rw [← show ((([(2, 4), (5, 1), (22571, 1), (648239, 1), (101815639, 1), (505935631, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441680 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_5, prime_fiftyOneAW_22571, prime_fiftyOneAW_648239, prime_fiftyOneAW_101815639, prime_fiftyOneAW_505935631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441681 : Nat.totient 60295611089243935643079441681 = 40197036705881922856606869504 := by
  rw [← show ((([(3, 7), (1076753, 1), (2179651489, 1), (11747183939, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441681 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_3, prime_fiftyOneAW_1076753, prime_fiftyOneAW_2179651489, prime_fiftyOneAW_11747183939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441682 : Nat.totient 60295611089243935643079441682 = 29315058104117381235425280000 := by
  rw [← show ((([(2, 1), (41, 1), (503, 1), (881, 1), (5197, 1), (250298611, 1), (1275606721, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441682 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_41, prime_fiftyOneAW_503, prime_fiftyOneAW_881, prime_fiftyOneAW_5197, prime_fiftyOneAW_250298611, prime_fiftyOneAW_1275606721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441683 : Nat.totient 60295611089243935643079441683 = 60295611089243935643079441682 := by
  rw [← show ((([(60295611089243935643079441683, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441683 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_60295611089243935643079441683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441684 : Nat.totient 60295611089243935643079441684 = 17227317251811354607377360000 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (122594851, 1), (282861461, 1), (20699526191, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441684 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_3, prime_fiftyOneAW_7, prime_fiftyOneAW_122594851, prime_fiftyOneAW_282861461, prime_fiftyOneAW_20699526191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441685 : Nat.totient 60295611089243935643079441685 = 45176271427153021317641256960 := by
  rw [← show ((([(5, 1), (17, 1), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441685 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_5, prime_fiftyOneAW_17, prime_fiftyOneAW_281, prime_fiftyOneAW_739, prime_fiftyOneAW_3540386347, prime_fiftyOneAW_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441686 : Nat.totient 60295611089243935643079441686 = 29400461852575442987070296640 := by
  rw [← show ((([(2, 1), (43, 1), (643, 1), (67411, 1), (16175045358502498537, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441686 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_43, prime_fiftyOneAW_643, prime_fiftyOneAW_67411, prime_fiftyOneAW_16175045358502498537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441687 : Nat.totient 60295611089243935643079441687 = 38576391891141802286644930560 := by
  rw [← show ((([(3, 1), (29, 1), (167, 1), (19421, 1), (223283, 1), (2432869, 1), (393372509, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441687 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_3, prime_fiftyOneAW_29, prime_fiftyOneAW_167, prime_fiftyOneAW_19421, prime_fiftyOneAW_223283, prime_fiftyOneAW_2432869, prime_fiftyOneAW_393372509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441688 : Nat.totient 60295611089243935643079441688 = 27407095233395227018337940480 := by
  rw [← show ((([(2, 3), (11, 1), (38264113, 1), (17906527684083735577, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441688 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_11, prime_fiftyOneAW_38264113, prime_fiftyOneAW_17906527684083735577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441689 : Nat.totient 60295611089243935643079441689 = 59276268572917958599758336000 := by
  rw [← show ((([(73, 1), (353, 1), (2381, 1), (982717613585267701301, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441689 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_73, prime_fiftyOneAW_353, prime_fiftyOneAW_2381, prime_fiftyOneAW_982717613585267701301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441690 : Nat.totient 60295611089243935643079441690 = 16008597900676221333899154048 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (229, 1), (865643, 1), (3379627908495294503, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441690 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_3, prime_fiftyOneAW_5, prime_fiftyOneAW_229, prime_fiftyOneAW_865643, prime_fiftyOneAW_3379627908495294503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441691 : Nat.totient 60295611089243935643079441691 = 47650795985477762719700572800 := by
  rw [← show ((([(7, 1), (13, 1), (859, 1), (878719, 1), (1578091, 1), (556248797191, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441691 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_7, prime_fiftyOneAW_13, prime_fiftyOneAW_859, prime_fiftyOneAW_878719, prime_fiftyOneAW_1578091, prime_fiftyOneAW_556248797191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441692 : Nat.totient 60295611089243935643079441692 = 28836791380438275499613872128 := by
  rw [← show ((([(2, 2), (23, 1), (120193, 1), (330134053, 1), (16516893739069, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441692 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_23, prime_fiftyOneAW_120193, prime_fiftyOneAW_330134053, prime_fiftyOneAW_16516893739069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441693 : Nat.totient 60295611089243935643079441693 = 38900394251125119769728672000 := by
  rw [← show ((([(3, 1), (31, 1), (648339904185418662828811201, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441693 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_3, prime_fiftyOneAW_31, prime_fiftyOneAW_648339904185418662828811201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441694 : Nat.totient 60295611089243935643079441694 = 28857015970223475967156224000 := by
  rw [← show ((([(2, 1), (47, 1), (79, 1), (113, 1), (1601, 1), (680171353, 1), (65984608471, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441694 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_47, prime_fiftyOneAW_79, prime_fiftyOneAW_113, prime_fiftyOneAW_1601, prime_fiftyOneAW_680171353, prime_fiftyOneAW_65984608471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441695 : Nat.totient 60295611089243935643079441695 = 45697681437021039563844860160 := by
  rw [← show ((([(5, 1), (19, 1), (1101641, 1), (13517267, 1), (42621930118723, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441695 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_5, prime_fiftyOneAW_19, prime_fiftyOneAW_1101641, prime_fiftyOneAW_13517267, prime_fiftyOneAW_42621930118723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441696 : Nat.totient 60295611089243935643079441696 = 20098534277997233877998377728 := by
  rw [← show ((([(2, 5), (3, 1), (7303909, 1), (85992210770920657639, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441696 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_3, prime_fiftyOneAW_7303909, prime_fiftyOneAW_85992210770920657639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441697 : Nat.totient 60295611089243935643079441697 = 60295611089243935643079441696 := by
  rw [← show ((([(60295611089243935643079441697, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441697 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_60295611089243935643079441697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441698 : Nat.totient 60295611089243935643079441698 = 25305050209504635305356320000 := by
  rw [← show ((([(2, 1), (7, 2), (71, 1), (151, 1), (8111, 1), (200297, 1), (35324456077943, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441698 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_7, prime_fiftyOneAW_71, prime_fiftyOneAW_151, prime_fiftyOneAW_8111, prime_fiftyOneAW_200297, prime_fiftyOneAW_35324456077943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441699 : Nat.totient 60295611089243935643079441699 = 36542783838998386926191808240 := by
  rw [← show ((([(3, 2), (11, 1), (3395999, 1), (179342389870853805599, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441699 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_3, prime_fiftyOneAW_11, prime_fiftyOneAW_3395999, prime_fiftyOneAW_179342389870853805599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyOneAW_60295611089243935643079441700 : Nat.totient 60295611089243935643079441700 = 23846364642595554769982976000 := by
  rw [← show ((([(2, 2), (5, 2), (89, 1), (36299, 1), (111187, 1), (1417541, 1), (1184162741, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243935643079441700 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyOneAW_2, prime_fiftyOneAW_5, prime_fiftyOneAW_89, prime_fiftyOneAW_36299, prime_fiftyOneAW_111187, prime_fiftyOneAW_1417541, prime_fiftyOneAW_1184162741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FiftyOneAW : certifiedKill 1 60295611089243935643079441599 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fiftyOneAW_60295611089243935643079441600, phi_fiftyOneAW_60295611089243935643079441601, phi_fiftyOneAW_60295611089243935643079441602,
    phi_fiftyOneAW_60295611089243935643079441603, phi_fiftyOneAW_60295611089243935643079441604, phi_fiftyOneAW_60295611089243935643079441605,
    phi_fiftyOneAW_60295611089243935643079441606, phi_fiftyOneAW_60295611089243935643079441607, phi_fiftyOneAW_60295611089243935643079441608,
    phi_fiftyOneAW_60295611089243935643079441609, phi_fiftyOneAW_60295611089243935643079441610, phi_fiftyOneAW_60295611089243935643079441611,
    phi_fiftyOneAW_60295611089243935643079441612, phi_fiftyOneAW_60295611089243935643079441613, phi_fiftyOneAW_60295611089243935643079441614,
    phi_fiftyOneAW_60295611089243935643079441615, phi_fiftyOneAW_60295611089243935643079441616, phi_fiftyOneAW_60295611089243935643079441617,
    phi_fiftyOneAW_60295611089243935643079441618, phi_fiftyOneAW_60295611089243935643079441619, phi_fiftyOneAW_60295611089243935643079441620,
    phi_fiftyOneAW_60295611089243935643079441621, phi_fiftyOneAW_60295611089243935643079441622, phi_fiftyOneAW_60295611089243935643079441623,
    phi_fiftyOneAW_60295611089243935643079441624, phi_fiftyOneAW_60295611089243935643079441625, phi_fiftyOneAW_60295611089243935643079441626,
    phi_fiftyOneAW_60295611089243935643079441627, phi_fiftyOneAW_60295611089243935643079441628, phi_fiftyOneAW_60295611089243935643079441629,
    phi_fiftyOneAW_60295611089243935643079441630, phi_fiftyOneAW_60295611089243935643079441631, phi_fiftyOneAW_60295611089243935643079441632,
    phi_fiftyOneAW_60295611089243935643079441633, phi_fiftyOneAW_60295611089243935643079441634, phi_fiftyOneAW_60295611089243935643079441635,
    phi_fiftyOneAW_60295611089243935643079441636, phi_fiftyOneAW_60295611089243935643079441637, phi_fiftyOneAW_60295611089243935643079441638,
    phi_fiftyOneAW_60295611089243935643079441639, phi_fiftyOneAW_60295611089243935643079441640, phi_fiftyOneAW_60295611089243935643079441641,
    phi_fiftyOneAW_60295611089243935643079441642, phi_fiftyOneAW_60295611089243935643079441643, phi_fiftyOneAW_60295611089243935643079441644,
    phi_fiftyOneAW_60295611089243935643079441645, phi_fiftyOneAW_60295611089243935643079441646, phi_fiftyOneAW_60295611089243935643079441647,
    phi_fiftyOneAW_60295611089243935643079441648, phi_fiftyOneAW_60295611089243935643079441649, phi_fiftyOneAW_60295611089243935643079441650,
    phi_fiftyOneAW_60295611089243935643079441651, phi_fiftyOneAW_60295611089243935643079441652, phi_fiftyOneAW_60295611089243935643079441653,
    phi_fiftyOneAW_60295611089243935643079441654, phi_fiftyOneAW_60295611089243935643079441655, phi_fiftyOneAW_60295611089243935643079441656,
    phi_fiftyOneAW_60295611089243935643079441657, phi_fiftyOneAW_60295611089243935643079441658, phi_fiftyOneAW_60295611089243935643079441659,
    phi_fiftyOneAW_60295611089243935643079441660, phi_fiftyOneAW_60295611089243935643079441661, phi_fiftyOneAW_60295611089243935643079441662,
    phi_fiftyOneAW_60295611089243935643079441663, phi_fiftyOneAW_60295611089243935643079441664, phi_fiftyOneAW_60295611089243935643079441665,
    phi_fiftyOneAW_60295611089243935643079441666, phi_fiftyOneAW_60295611089243935643079441667, phi_fiftyOneAW_60295611089243935643079441668,
    phi_fiftyOneAW_60295611089243935643079441669, phi_fiftyOneAW_60295611089243935643079441670, phi_fiftyOneAW_60295611089243935643079441671,
    phi_fiftyOneAW_60295611089243935643079441672, phi_fiftyOneAW_60295611089243935643079441673, phi_fiftyOneAW_60295611089243935643079441674,
    phi_fiftyOneAW_60295611089243935643079441675, phi_fiftyOneAW_60295611089243935643079441676, phi_fiftyOneAW_60295611089243935643079441677,
    phi_fiftyOneAW_60295611089243935643079441678, phi_fiftyOneAW_60295611089243935643079441679, phi_fiftyOneAW_60295611089243935643079441680,
    phi_fiftyOneAW_60295611089243935643079441681, phi_fiftyOneAW_60295611089243935643079441682, phi_fiftyOneAW_60295611089243935643079441683,
    phi_fiftyOneAW_60295611089243935643079441684, phi_fiftyOneAW_60295611089243935643079441685, phi_fiftyOneAW_60295611089243935643079441686,
    phi_fiftyOneAW_60295611089243935643079441687, phi_fiftyOneAW_60295611089243935643079441688, phi_fiftyOneAW_60295611089243935643079441689,
    phi_fiftyOneAW_60295611089243935643079441690, phi_fiftyOneAW_60295611089243935643079441691, phi_fiftyOneAW_60295611089243935643079441692,
    phi_fiftyOneAW_60295611089243935643079441693, phi_fiftyOneAW_60295611089243935643079441694, phi_fiftyOneAW_60295611089243935643079441695,
    phi_fiftyOneAW_60295611089243935643079441696, phi_fiftyOneAW_60295611089243935643079441697, phi_fiftyOneAW_60295611089243935643079441698,
    phi_fiftyOneAW_60295611089243935643079441699, phi_fiftyOneAW_60295611089243935643079441700
  ]

end TotientTailPeriodKiller
end Erdos249257
