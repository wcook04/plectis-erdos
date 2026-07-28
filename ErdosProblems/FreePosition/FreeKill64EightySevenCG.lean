import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def eightySevenCGFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem eightySevenCGFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : eightySevenCGFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [eightySevenCGFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [eightySevenCGFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then eightySevenCGFastPow a n * eightySevenCGFastPow a n * a else eightySevenCGFastPow a n * eightySevenCGFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_eightySevenCG_2 : Nat.Prime 2 := by norm_num

private theorem prime_eightySevenCG_3 : Nat.Prime 3 := by norm_num

private theorem prime_eightySevenCG_5 : Nat.Prime 5 := by norm_num

private theorem prime_eightySevenCG_7 : Nat.Prime 7 := by norm_num

private theorem prime_eightySevenCG_11 : Nat.Prime 11 := by norm_num

private theorem prime_eightySevenCG_13 : Nat.Prime 13 := by norm_num

private theorem prime_eightySevenCG_17 : Nat.Prime 17 := by norm_num

private theorem prime_eightySevenCG_19 : Nat.Prime 19 := by norm_num

private theorem prime_eightySevenCG_23 : Nat.Prime 23 := by norm_num

private theorem prime_eightySevenCG_29 : Nat.Prime 29 := by norm_num

private theorem prime_eightySevenCG_31 : Nat.Prime 31 := by norm_num

private theorem prime_eightySevenCG_37 : Nat.Prime 37 := by norm_num

private theorem prime_eightySevenCG_41 : Nat.Prime 41 := by norm_num

private theorem prime_eightySevenCG_43 : Nat.Prime 43 := by norm_num

private theorem prime_eightySevenCG_47 : Nat.Prime 47 := by norm_num

private theorem prime_eightySevenCG_53 : Nat.Prime 53 := by norm_num

private theorem prime_eightySevenCG_59 : Nat.Prime 59 := by norm_num

private theorem prime_eightySevenCG_61 : Nat.Prime 61 := by norm_num

private theorem prime_eightySevenCG_67 : Nat.Prime 67 := by norm_num

private theorem prime_eightySevenCG_71 : Nat.Prime 71 := by norm_num

private theorem prime_eightySevenCG_73 : Nat.Prime 73 := by norm_num

private theorem prime_eightySevenCG_79 : Nat.Prime 79 := by norm_num

private theorem prime_eightySevenCG_83 : Nat.Prime 83 := by norm_num

private theorem prime_eightySevenCG_89 : Nat.Prime 89 := by norm_num

private theorem prime_eightySevenCG_97 : Nat.Prime 97 := by norm_num

private theorem prime_eightySevenCG_101 : Nat.Prime 101 := by norm_num

private theorem prime_eightySevenCG_103 : Nat.Prime 103 := by norm_num

private theorem prime_eightySevenCG_107 : Nat.Prime 107 := by norm_num

private theorem prime_eightySevenCG_109 : Nat.Prime 109 := by norm_num

private theorem prime_eightySevenCG_113 : Nat.Prime 113 := by norm_num

private theorem prime_eightySevenCG_127 : Nat.Prime 127 := by norm_num

private theorem prime_eightySevenCG_131 : Nat.Prime 131 := by norm_num

private theorem prime_eightySevenCG_137 : Nat.Prime 137 := by norm_num

private theorem prime_eightySevenCG_139 : Nat.Prime 139 := by norm_num

private theorem prime_eightySevenCG_149 : Nat.Prime 149 := by norm_num

private theorem prime_eightySevenCG_151 : Nat.Prime 151 := by norm_num

private theorem prime_eightySevenCG_157 : Nat.Prime 157 := by norm_num

private theorem prime_eightySevenCG_163 : Nat.Prime 163 := by norm_num

private theorem prime_eightySevenCG_167 : Nat.Prime 167 := by norm_num

private theorem prime_eightySevenCG_173 : Nat.Prime 173 := by norm_num

private theorem prime_eightySevenCG_179 : Nat.Prime 179 := by norm_num

private theorem prime_eightySevenCG_181 : Nat.Prime 181 := by norm_num

private theorem prime_eightySevenCG_191 : Nat.Prime 191 := by norm_num

private theorem prime_eightySevenCG_193 : Nat.Prime 193 := by norm_num

private theorem prime_eightySevenCG_197 : Nat.Prime 197 := by norm_num

private theorem prime_eightySevenCG_199 : Nat.Prime 199 := by norm_num

private theorem prime_eightySevenCG_211 : Nat.Prime 211 := by norm_num

private theorem prime_eightySevenCG_223 : Nat.Prime 223 := by norm_num

private theorem prime_eightySevenCG_227 : Nat.Prime 227 := by norm_num

private theorem prime_eightySevenCG_229 : Nat.Prime 229 := by norm_num

private theorem prime_eightySevenCG_233 : Nat.Prime 233 := by norm_num

private theorem prime_eightySevenCG_241 : Nat.Prime 241 := by norm_num

private theorem prime_eightySevenCG_251 : Nat.Prime 251 := by norm_num

private theorem prime_eightySevenCG_257 : Nat.Prime 257 := by norm_num

private theorem prime_eightySevenCG_269 : Nat.Prime 269 := by norm_num

private theorem prime_eightySevenCG_277 : Nat.Prime 277 := by norm_num

private theorem prime_eightySevenCG_281 : Nat.Prime 281 := by norm_num

private theorem prime_eightySevenCG_293 : Nat.Prime 293 := by norm_num

private theorem prime_eightySevenCG_307 : Nat.Prime 307 := by norm_num

private theorem prime_eightySevenCG_311 : Nat.Prime 311 := by norm_num

private theorem prime_eightySevenCG_313 : Nat.Prime 313 := by norm_num

private theorem prime_eightySevenCG_317 : Nat.Prime 317 := by norm_num

private theorem prime_eightySevenCG_331 : Nat.Prime 331 := by norm_num

private theorem prime_eightySevenCG_337 : Nat.Prime 337 := by norm_num

private theorem prime_eightySevenCG_347 : Nat.Prime 347 := by norm_num

private theorem prime_eightySevenCG_353 : Nat.Prime 353 := by norm_num

private theorem prime_eightySevenCG_359 : Nat.Prime 359 := by norm_num

private theorem prime_eightySevenCG_367 : Nat.Prime 367 := by norm_num

private theorem prime_eightySevenCG_373 : Nat.Prime 373 := by norm_num

private theorem prime_eightySevenCG_397 : Nat.Prime 397 := by norm_num

private theorem prime_eightySevenCG_401 : Nat.Prime 401 := by norm_num

private theorem prime_eightySevenCG_431 : Nat.Prime 431 := by norm_num

private theorem prime_eightySevenCG_433 : Nat.Prime 433 := by norm_num

private theorem prime_eightySevenCG_443 : Nat.Prime 443 := by norm_num

private theorem prime_eightySevenCG_449 : Nat.Prime 449 := by norm_num

private theorem prime_eightySevenCG_461 : Nat.Prime 461 := by norm_num

private theorem prime_eightySevenCG_491 : Nat.Prime 491 := by norm_num

private theorem prime_eightySevenCG_499 : Nat.Prime 499 := by norm_num

private theorem prime_eightySevenCG_521 : Nat.Prime 521 := by norm_num

private theorem prime_eightySevenCG_541 : Nat.Prime 541 := by norm_num

private theorem prime_eightySevenCG_547 : Nat.Prime 547 := by norm_num

private theorem prime_eightySevenCG_557 : Nat.Prime 557 := by norm_num

private theorem prime_eightySevenCG_569 : Nat.Prime 569 := by norm_num

private theorem prime_eightySevenCG_571 : Nat.Prime 571 := by norm_num

private theorem prime_eightySevenCG_577 : Nat.Prime 577 := by norm_num

private theorem prime_eightySevenCG_587 : Nat.Prime 587 := by norm_num

private theorem prime_eightySevenCG_599 : Nat.Prime 599 := by norm_num

private theorem prime_eightySevenCG_607 : Nat.Prime 607 := by norm_num

private theorem prime_eightySevenCG_613 : Nat.Prime 613 := by norm_num

private theorem prime_eightySevenCG_619 : Nat.Prime 619 := by norm_num

private theorem prime_eightySevenCG_641 : Nat.Prime 641 := by norm_num

private theorem prime_eightySevenCG_643 : Nat.Prime 643 := by norm_num

private theorem prime_eightySevenCG_653 : Nat.Prime 653 := by norm_num

private theorem prime_eightySevenCG_659 : Nat.Prime 659 := by norm_num

private theorem prime_eightySevenCG_677 : Nat.Prime 677 := by norm_num

private theorem prime_eightySevenCG_683 : Nat.Prime 683 := by norm_num

private theorem prime_eightySevenCG_691 : Nat.Prime 691 := by norm_num

private theorem prime_eightySevenCG_701 : Nat.Prime 701 := by norm_num

private theorem prime_eightySevenCG_709 : Nat.Prime 709 := by norm_num

private theorem prime_eightySevenCG_739 : Nat.Prime 739 := by norm_num

private theorem prime_eightySevenCG_743 : Nat.Prime 743 := by norm_num

private theorem prime_eightySevenCG_757 : Nat.Prime 757 := by norm_num

private theorem prime_eightySevenCG_761 : Nat.Prime 761 := by norm_num

private theorem prime_eightySevenCG_773 : Nat.Prime 773 := by norm_num

private theorem prime_eightySevenCG_809 : Nat.Prime 809 := by norm_num

private theorem prime_eightySevenCG_811 : Nat.Prime 811 := by norm_num

private theorem prime_eightySevenCG_839 : Nat.Prime 839 := by norm_num

private theorem prime_eightySevenCG_853 : Nat.Prime 853 := by norm_num

private theorem prime_eightySevenCG_859 : Nat.Prime 859 := by norm_num

private theorem prime_eightySevenCG_919 : Nat.Prime 919 := by norm_num

private theorem prime_eightySevenCG_941 : Nat.Prime 941 := by norm_num

private theorem prime_eightySevenCG_971 : Nat.Prime 971 := by norm_num

private theorem prime_eightySevenCG_977 : Nat.Prime 977 := by norm_num

private theorem prime_eightySevenCG_983 : Nat.Prime 983 := by norm_num

private theorem prime_eightySevenCG_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_eightySevenCG_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_eightySevenCG_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_eightySevenCG_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_eightySevenCG_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_eightySevenCG_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_eightySevenCG_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_eightySevenCG_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_eightySevenCG_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_eightySevenCG_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_eightySevenCG_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_eightySevenCG_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_eightySevenCG_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_eightySevenCG_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_eightySevenCG_1559 : Nat.Prime 1559 := by norm_num

private theorem prime_eightySevenCG_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_eightySevenCG_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_eightySevenCG_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_eightySevenCG_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_eightySevenCG_1657 : Nat.Prime 1657 := by norm_num

private theorem prime_eightySevenCG_1697 : Nat.Prime 1697 := by norm_num

private theorem prime_eightySevenCG_1709 : Nat.Prime 1709 := by norm_num

private theorem prime_eightySevenCG_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_eightySevenCG_1789 : Nat.Prime 1789 := by norm_num

private theorem prime_eightySevenCG_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_eightySevenCG_1823 : Nat.Prime 1823 := by norm_num

private theorem prime_eightySevenCG_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_eightySevenCG_1871 : Nat.Prime 1871 := by norm_num

private theorem prime_eightySevenCG_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_eightySevenCG_1889 : Nat.Prime 1889 := by norm_num

private theorem prime_eightySevenCG_2083 : Nat.Prime 2083 := by norm_num

private theorem prime_eightySevenCG_2087 : Nat.Prime 2087 := by norm_num

private theorem prime_eightySevenCG_2267 : Nat.Prime 2267 := by norm_num

private theorem prime_eightySevenCG_2417 : Nat.Prime 2417 := by norm_num

private theorem prime_eightySevenCG_2423 : Nat.Prime 2423 := by norm_num

private theorem prime_eightySevenCG_2459 : Nat.Prime 2459 := by norm_num

private theorem prime_eightySevenCG_2467 : Nat.Prime 2467 := by norm_num

private theorem prime_eightySevenCG_2473 : Nat.Prime 2473 := by norm_num

private theorem prime_eightySevenCG_2693 : Nat.Prime 2693 := by norm_num

private theorem prime_eightySevenCG_2731 : Nat.Prime 2731 := by norm_num

private theorem prime_eightySevenCG_2833 : Nat.Prime 2833 := by norm_num

private theorem prime_eightySevenCG_2957 : Nat.Prime 2957 := by norm_num

private theorem prime_eightySevenCG_3001 : Nat.Prime 3001 := by norm_num

private theorem prime_eightySevenCG_3119 : Nat.Prime 3119 := by norm_num

private theorem prime_eightySevenCG_3191 : Nat.Prime 3191 := by norm_num

private theorem prime_eightySevenCG_3209 : Nat.Prime 3209 := by norm_num

private theorem prime_eightySevenCG_3259 : Nat.Prime 3259 := by norm_num

private theorem prime_eightySevenCG_3299 : Nat.Prime 3299 := by norm_num

private theorem prime_eightySevenCG_3511 : Nat.Prime 3511 := by norm_num

private theorem prime_eightySevenCG_3547 : Nat.Prime 3547 := by norm_num

private theorem prime_eightySevenCG_3593 : Nat.Prime 3593 := by norm_num

private theorem prime_eightySevenCG_3617 : Nat.Prime 3617 := by norm_num

private theorem prime_eightySevenCG_3631 : Nat.Prime 3631 := by norm_num

private theorem prime_eightySevenCG_3677 : Nat.Prime 3677 := by norm_num

private theorem prime_eightySevenCG_3823 : Nat.Prime 3823 := by norm_num

private theorem prime_eightySevenCG_3917 : Nat.Prime 3917 := by norm_num

private theorem prime_eightySevenCG_4057 : Nat.Prime 4057 := by norm_num

private theorem prime_eightySevenCG_4219 : Nat.Prime 4219 := by norm_num

private theorem prime_eightySevenCG_4397 : Nat.Prime 4397 := by norm_num

private theorem prime_eightySevenCG_5009 : Nat.Prime 5009 := by norm_num

private theorem prime_eightySevenCG_5059 : Nat.Prime 5059 := by norm_num

private theorem prime_eightySevenCG_5087 : Nat.Prime 5087 := by norm_num

private theorem prime_eightySevenCG_5171 : Nat.Prime 5171 := by norm_num

private theorem prime_eightySevenCG_5189 : Nat.Prime 5189 := by norm_num

private theorem prime_eightySevenCG_5323 : Nat.Prime 5323 := by norm_num

private theorem prime_eightySevenCG_5471 : Nat.Prime 5471 := by norm_num

private theorem prime_eightySevenCG_5527 : Nat.Prime 5527 := by norm_num

private theorem prime_eightySevenCG_6101 : Nat.Prime 6101 := by norm_num

private theorem prime_eightySevenCG_6113 : Nat.Prime 6113 := by norm_num

private theorem prime_eightySevenCG_6491 : Nat.Prime 6491 := by norm_num

private theorem prime_eightySevenCG_6673 : Nat.Prime 6673 := by norm_num

private theorem prime_eightySevenCG_6883 : Nat.Prime 6883 := by norm_num

private theorem prime_eightySevenCG_7351 : Nat.Prime 7351 := by norm_num

private theorem prime_eightySevenCG_7433 : Nat.Prime 7433 := by norm_num

private theorem prime_eightySevenCG_7789 : Nat.Prime 7789 := by norm_num

private theorem prime_eightySevenCG_7793 : Nat.Prime 7793 := by norm_num

private theorem prime_eightySevenCG_7867 : Nat.Prime 7867 := by norm_num

private theorem prime_eightySevenCG_7933 : Nat.Prime 7933 := by norm_num

private theorem prime_eightySevenCG_8161 : Nat.Prime 8161 := by norm_num

private theorem prime_eightySevenCG_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_eightySevenCG_8599 : Nat.Prime 8599 := by norm_num

private theorem prime_eightySevenCG_8951 : Nat.Prime 8951 := by norm_num

private theorem prime_eightySevenCG_9551 : Nat.Prime 9551 := by norm_num

private theorem prime_eightySevenCG_10459 : Nat.Prime 10459 := by norm_num

private theorem prime_eightySevenCG_10477 : Nat.Prime 10477 := by norm_num

private theorem prime_eightySevenCG_11867 : Nat.Prime 11867 := by norm_num

private theorem prime_eightySevenCG_12583 : Nat.Prime 12583 := by norm_num

private theorem prime_eightySevenCG_12799 : Nat.Prime 12799 := by norm_num

private theorem prime_eightySevenCG_13043 : Nat.Prime 13043 := by norm_num

private theorem prime_eightySevenCG_13099 : Nat.Prime 13099 := by norm_num

private theorem prime_eightySevenCG_13109 : Nat.Prime 13109 := by norm_num

private theorem prime_eightySevenCG_13217 : Nat.Prime 13217 := by norm_num

private theorem prime_eightySevenCG_13339 : Nat.Prime 13339 := by norm_num

private theorem prime_eightySevenCG_13417 : Nat.Prime 13417 := by norm_num

private theorem prime_eightySevenCG_13933 : Nat.Prime 13933 := by norm_num

private theorem prime_eightySevenCG_15641 : Nat.Prime 15641 := by norm_num

private theorem prime_eightySevenCG_16493 : Nat.Prime 16493 := by norm_num

private theorem prime_eightySevenCG_16661 : Nat.Prime 16661 := by norm_num

private theorem prime_eightySevenCG_16931 : Nat.Prime 16931 := by norm_num

private theorem prime_eightySevenCG_17389 : Nat.Prime 17389 := by norm_num

private theorem prime_eightySevenCG_21319 : Nat.Prime 21319 := by norm_num

private theorem prime_eightySevenCG_22283 : Nat.Prime 22283 := by norm_num

private theorem prime_eightySevenCG_22381 : Nat.Prime 22381 := by norm_num

private theorem prime_eightySevenCG_23671 : Nat.Prime 23671 := by norm_num

private theorem prime_eightySevenCG_23741 : Nat.Prime 23741 := by norm_num

private theorem prime_eightySevenCG_23857 : Nat.Prime 23857 := by norm_num

private theorem prime_eightySevenCG_23917 : Nat.Prime 23917 := by norm_num

private theorem prime_eightySevenCG_24527 : Nat.Prime 24527 := by norm_num

private theorem prime_eightySevenCG_25601 : Nat.Prime 25601 := by norm_num

private theorem prime_eightySevenCG_25633 : Nat.Prime 25633 := by norm_num

private theorem prime_eightySevenCG_26203 : Nat.Prime 26203 := by norm_num

private theorem prime_eightySevenCG_26407 : Nat.Prime 26407 := by norm_num

private theorem prime_eightySevenCG_26717 : Nat.Prime 26717 := by norm_num

private theorem prime_eightySevenCG_28627 : Nat.Prime 28627 := by norm_num

private theorem prime_eightySevenCG_30313 : Nat.Prime 30313 := by norm_num

private theorem prime_eightySevenCG_31139 : Nat.Prime 31139 := by norm_num

private theorem prime_eightySevenCG_33647 : Nat.Prime 33647 := by norm_num

private theorem prime_eightySevenCG_34129 : Nat.Prime 34129 := by norm_num

private theorem prime_eightySevenCG_34591 : Nat.Prime 34591 := by norm_num

private theorem prime_eightySevenCG_34843 : Nat.Prime 34843 := by norm_num

private theorem prime_eightySevenCG_35747 : Nat.Prime 35747 := by norm_num

private theorem prime_eightySevenCG_36161 : Nat.Prime 36161 := by norm_num

private theorem prime_eightySevenCG_37493 : Nat.Prime 37493 := by norm_num

private theorem prime_eightySevenCG_37571 : Nat.Prime 37571 := by norm_num

private theorem prime_eightySevenCG_37589 : Nat.Prime 37589 := by norm_num

private theorem prime_eightySevenCG_44041 : Nat.Prime 44041 := by norm_num

private theorem prime_eightySevenCG_45433 : Nat.Prime 45433 := by norm_num

private theorem prime_eightySevenCG_51437 : Nat.Prime 51437 := by norm_num

private theorem prime_eightySevenCG_51481 : Nat.Prime 51481 := by norm_num

private theorem prime_eightySevenCG_51637 : Nat.Prime 51637 := by norm_num

private theorem prime_eightySevenCG_54601 : Nat.Prime 54601 := by norm_num

private theorem prime_eightySevenCG_55339 : Nat.Prime 55339 := by norm_num

private theorem prime_eightySevenCG_58741 : Nat.Prime 58741 := by norm_num

private theorem prime_eightySevenCG_63841 : Nat.Prime 63841 := by norm_num

private theorem prime_eightySevenCG_66377 : Nat.Prime 66377 := by norm_num

private theorem prime_eightySevenCG_69067 : Nat.Prime 69067 := by norm_num

private theorem prime_eightySevenCG_69821 : Nat.Prime 69821 := by norm_num

private theorem prime_eightySevenCG_70321 : Nat.Prime 70321 := by norm_num

private theorem prime_eightySevenCG_70583 : Nat.Prime 70583 := by norm_num

private theorem prime_eightySevenCG_73351 : Nat.Prime 73351 := by norm_num

private theorem prime_eightySevenCG_73709 : Nat.Prime 73709 := by norm_num

private theorem prime_eightySevenCG_76717 : Nat.Prime 76717 := by norm_num

private theorem prime_eightySevenCG_78031 : Nat.Prime 78031 := by norm_num

private theorem prime_eightySevenCG_80687 : Nat.Prime 80687 := by norm_num

private theorem prime_eightySevenCG_85667 : Nat.Prime 85667 := by norm_num

private theorem prime_eightySevenCG_90481 : Nat.Prime 90481 := by norm_num

private theorem prime_eightySevenCG_97381 : Nat.Prime 97381 := by norm_num

private theorem prime_eightySevenCG_99013 : Nat.Prime 99013 := by norm_num

private theorem prime_eightySevenCG_102587 : Nat.Prime 102587 := by norm_num

private theorem prime_eightySevenCG_104551 : Nat.Prime 104551 := by norm_num

private theorem prime_eightySevenCG_106979 : Nat.Prime 106979 := by norm_num

private theorem prime_eightySevenCG_111341 : Nat.Prime 111341 := by norm_num

private theorem prime_eightySevenCG_113383 : Nat.Prime 113383 := by norm_num

private theorem prime_eightySevenCG_114833 : Nat.Prime 114833 := by norm_num

private theorem prime_eightySevenCG_115781 : Nat.Prime 115781 := by norm_num

private theorem prime_eightySevenCG_118619 : Nat.Prime 118619 := by norm_num

private theorem prime_eightySevenCG_120691 : Nat.Prime 120691 := by norm_num

private theorem prime_eightySevenCG_141679 : Nat.Prime 141679 := by norm_num

private theorem prime_eightySevenCG_141961 : Nat.Prime 141961 := by norm_num

private theorem prime_eightySevenCG_177953 : Nat.Prime 177953 := by norm_num

private theorem prime_eightySevenCG_179827 : Nat.Prime 179827 := by norm_num

private theorem prime_eightySevenCG_187163 : Nat.Prime 187163 := by norm_num

private theorem prime_eightySevenCG_189473 : Nat.Prime 189473 := by norm_num

private theorem prime_eightySevenCG_223211 : Nat.Prime 223211 := by norm_num

private theorem prime_eightySevenCG_224101 : Nat.Prime 224101 := by norm_num

private theorem prime_eightySevenCG_225217 : Nat.Prime 225217 := by norm_num

private theorem prime_eightySevenCG_229213 : Nat.Prime 229213 := by norm_num

private theorem prime_eightySevenCG_233917 : Nat.Prime 233917 := by norm_num

private theorem prime_eightySevenCG_237157 : Nat.Prime 237157 := by norm_num

private theorem prime_eightySevenCG_239383 : Nat.Prime 239383 := by norm_num

private theorem prime_eightySevenCG_255947 : Nat.Prime 255947 := by norm_num

private theorem prime_eightySevenCG_257273 : Nat.Prime 257273 := by norm_num

private theorem prime_eightySevenCG_274237 : Nat.Prime 274237 := by norm_num

private theorem prime_eightySevenCG_285871 : Nat.Prime 285871 := by norm_num

private theorem prime_eightySevenCG_292079 : Nat.Prime 292079 := by norm_num

private theorem prime_eightySevenCG_292309 : Nat.Prime 292309 := by norm_num

private theorem prime_eightySevenCG_318841 : Nat.Prime 318841 := by norm_num

private theorem prime_eightySevenCG_324781 : Nat.Prime 324781 := by norm_num

private theorem prime_eightySevenCG_327491 : Nat.Prime 327491 := by norm_num

private theorem prime_eightySevenCG_370471 : Nat.Prime 370471 := by norm_num

private theorem prime_eightySevenCG_424913 : Nat.Prime 424913 := by norm_num

private theorem prime_eightySevenCG_441011 : Nat.Prime 441011 := by norm_num

private theorem prime_eightySevenCG_450277 : Nat.Prime 450277 := by norm_num

private theorem prime_eightySevenCG_452269 : Nat.Prime 452269 := by norm_num

private theorem prime_eightySevenCG_465041 : Nat.Prime 465041 := by norm_num

private theorem prime_eightySevenCG_478843 : Nat.Prime 478843 := by norm_num

private theorem prime_eightySevenCG_483377 : Nat.Prime 483377 := by norm_num

private theorem prime_eightySevenCG_513059 : Nat.Prime 513059 := by norm_num

private theorem prime_eightySevenCG_519907 : Nat.Prime 519907 := by norm_num

private theorem prime_eightySevenCG_560411 : Nat.Prime 560411 := by norm_num

private theorem prime_eightySevenCG_562357 : Nat.Prime 562357 := by norm_num

private theorem prime_eightySevenCG_565337 : Nat.Prime 565337 := by norm_num

private theorem prime_eightySevenCG_573343 : Nat.Prime 573343 := by norm_num

private theorem prime_eightySevenCG_584531 : Nat.Prime 584531 := by norm_num

private theorem prime_eightySevenCG_584873 : Nat.Prime 584873 := by norm_num

private theorem prime_eightySevenCG_598853 : Nat.Prime 598853 := by norm_num

private theorem prime_eightySevenCG_604819 : Nat.Prime 604819 := by norm_num

private theorem prime_eightySevenCG_605147 : Nat.Prime 605147 := by norm_num

private theorem prime_eightySevenCG_618053 : Nat.Prime 618053 := by norm_num

private theorem prime_eightySevenCG_632851 : Nat.Prime 632851 := by norm_num

private theorem prime_eightySevenCG_636211 : Nat.Prime 636211 := by norm_num

private theorem prime_eightySevenCG_641299 : Nat.Prime 641299 := by norm_num

private theorem prime_eightySevenCG_647917 : Nat.Prime 647917 := by norm_num

private theorem prime_eightySevenCG_677473 : Nat.Prime 677473 := by norm_num

private theorem prime_eightySevenCG_723803 : Nat.Prime 723803 := by norm_num

private theorem prime_eightySevenCG_751103 : Nat.Prime 751103 := by norm_num

private theorem prime_eightySevenCG_776057 : Nat.Prime 776057 := by norm_num

private theorem prime_eightySevenCG_865783 : Nat.Prime 865783 := by norm_num

private theorem prime_eightySevenCG_909863 : Nat.Prime 909863 := by norm_num

private theorem prime_eightySevenCG_928979 : Nat.Prime 928979 := by norm_num

private theorem prime_eightySevenCG_954253 : Nat.Prime 954253 := by norm_num

private theorem prime_eightySevenCG_1071977 : Nat.Prime 1071977 := by norm_num

private theorem prime_eightySevenCG_1383377 : Nat.Prime 1383377 := by norm_num

private theorem prime_eightySevenCG_1384343 : Nat.Prime 1384343 := by norm_num

private theorem prime_eightySevenCG_1391183 : Nat.Prime 1391183 := by norm_num

private theorem prime_eightySevenCG_1630133 : Nat.Prime 1630133 := by norm_num

private theorem prime_eightySevenCG_1661273 : Nat.Prime 1661273 := by norm_num

private theorem prime_eightySevenCG_1684301 : Nat.Prime 1684301 := by norm_num

private theorem prime_eightySevenCG_1750069 : Nat.Prime 1750069 := by norm_num

private theorem prime_eightySevenCG_1750607 : Nat.Prime 1750607 := by norm_num

private theorem prime_eightySevenCG_1829389 : Nat.Prime 1829389 := by norm_num

private theorem prime_eightySevenCG_1849171 : Nat.Prime 1849171 := by norm_num

private theorem prime_eightySevenCG_1885529 : Nat.Prime 1885529 := by norm_num

private theorem prime_eightySevenCG_2037803 : Nat.Prime 2037803 := by norm_num

private theorem prime_eightySevenCG_2088343 : Nat.Prime 2088343 := by norm_num

private theorem prime_eightySevenCG_2166607 : Nat.Prime 2166607 := by norm_num

private theorem prime_eightySevenCG_2178679 : Nat.Prime 2178679 := by norm_num

private theorem prime_eightySevenCG_2220367 : Nat.Prime 2220367 := by norm_num

private theorem prime_eightySevenCG_2428037 : Nat.Prime 2428037 := by norm_num

private theorem prime_eightySevenCG_2615903 : Nat.Prime 2615903 := by norm_num

private theorem prime_eightySevenCG_2653097 : Nat.Prime 2653097 := by norm_num

private theorem prime_eightySevenCG_2703031 : Nat.Prime 2703031 := by norm_num

private theorem prime_eightySevenCG_2742563 : Nat.Prime 2742563 := by norm_num

private theorem prime_eightySevenCG_2962273 : Nat.Prime 2962273 := by norm_num

private theorem prime_eightySevenCG_2980993 : Nat.Prime 2980993 := by norm_num

private theorem prime_eightySevenCG_3223439 : Nat.Prime 3223439 := by norm_num

private theorem prime_eightySevenCG_3396377 : Nat.Prime 3396377 := by norm_num

private theorem prime_eightySevenCG_3461369 : Nat.Prime 3461369 := by norm_num

private theorem prime_eightySevenCG_3535163 : Nat.Prime 3535163 := by norm_num

private theorem prime_eightySevenCG_3694319 : Nat.Prime 3694319 := by norm_num

private theorem prime_eightySevenCG_3985567 : Nat.Prime 3985567 := by norm_num

private theorem prime_eightySevenCG_4107577 : Nat.Prime 4107577 := by norm_num

private theorem prime_eightySevenCG_4215697 : Nat.Prime 4215697 := by norm_num

private theorem prime_eightySevenCG_4296977 : Nat.Prime 4296977 := by norm_num

private theorem prime_eightySevenCG_4547567 : Nat.Prime 4547567 := by norm_num

private theorem prime_eightySevenCG_4719607 : Nat.Prime 4719607 := by norm_num

private theorem prime_eightySevenCG_4907437 : Nat.Prime 4907437 := by norm_num

private theorem prime_eightySevenCG_4959523 : Nat.Prime 4959523 := by norm_num

private theorem prime_eightySevenCG_5091199 : Nat.Prime 5091199 := by norm_num

private theorem prime_eightySevenCG_5264291 : Nat.Prime 5264291 := by norm_num

private theorem prime_eightySevenCG_5509081 : Nat.Prime 5509081 := by norm_num

private theorem prime_eightySevenCG_5598119 : Nat.Prime 5598119 := by norm_num

private theorem prime_eightySevenCG_5677699 : Nat.Prime 5677699 := by norm_num

private theorem prime_eightySevenCG_5857399 : Nat.Prime 5857399 := by norm_num

private theorem prime_eightySevenCG_5968817 : Nat.Prime 5968817 := by norm_num

private theorem prime_eightySevenCG_6064703 : Nat.Prime 6064703 := by norm_num

private theorem prime_eightySevenCG_6180127 : Nat.Prime 6180127 := by norm_num

private theorem prime_eightySevenCG_6222551 : Nat.Prime 6222551 := by norm_num

private theorem prime_eightySevenCG_7095761 : Nat.Prime 7095761 := by norm_num

private theorem prime_eightySevenCG_7163017 : Nat.Prime 7163017 := by norm_num

private theorem prime_eightySevenCG_7280089 : Nat.Prime 7280089 := by norm_num

private theorem prime_eightySevenCG_7445287 : Nat.Prime 7445287 := by norm_num

private theorem prime_eightySevenCG_7512437 : Nat.Prime 7512437 := by norm_num

private theorem prime_eightySevenCG_7726051 : Nat.Prime 7726051 := by norm_num

private theorem prime_eightySevenCG_7740091 : Nat.Prime 7740091 := by norm_num

private theorem prime_eightySevenCG_7983617 : Nat.Prime 7983617 := by norm_num

private theorem prime_eightySevenCG_8197339 : Nat.Prime 8197339 := by norm_num

private theorem prime_eightySevenCG_8382713 : Nat.Prime 8382713 := by norm_num

private theorem prime_eightySevenCG_8440373 : Nat.Prime 8440373 := by norm_num

private theorem prime_eightySevenCG_8713109 : Nat.Prime 8713109 := by norm_num

private theorem prime_eightySevenCG_8756299 : Nat.Prime 8756299 := by norm_num

private theorem prime_eightySevenCG_9041741 : Nat.Prime 9041741 := by norm_num

private theorem prime_eightySevenCG_9196273 : Nat.Prime 9196273 := by norm_num

private theorem prime_eightySevenCG_9251017 : Nat.Prime 9251017 := by norm_num

private theorem prime_eightySevenCG_9266503 : Nat.Prime 9266503 := by norm_num

private theorem prime_eightySevenCG_9485797 : Nat.Prime 9485797 := by norm_num

private theorem prime_eightySevenCG_9845677 : Nat.Prime 9845677 := by norm_num

private theorem prime_eightySevenCG_10010431 : Nat.Prime 10010431 := by norm_num

private theorem prime_eightySevenCG_10089103 : Nat.Prime 10089103 := by norm_num

private theorem prime_eightySevenCG_10977259 : Nat.Prime 10977259 := by norm_num

private theorem prime_eightySevenCG_11475623 : Nat.Prime 11475623 := by norm_num

private theorem prime_eightySevenCG_11792419 : Nat.Prime 11792419 := by norm_num

private theorem prime_eightySevenCG_12156847 : Nat.Prime 12156847 := by norm_num

private theorem prime_eightySevenCG_12706711 : Nat.Prime 12706711 := by norm_num

private theorem prime_eightySevenCG_12828997 : Nat.Prime 12828997 := by norm_num

private theorem prime_eightySevenCG_13702859 : Nat.Prime 13702859 := by norm_num

private theorem prime_eightySevenCG_14837197 : Nat.Prime 14837197 := by norm_num

private theorem prime_eightySevenCG_15042571 : Nat.Prime 15042571 := by norm_num

private theorem prime_eightySevenCG_17372483 : Nat.Prime 17372483 := by norm_num

private theorem prime_eightySevenCG_17495521 : Nat.Prime 17495521 := by norm_num

private theorem prime_eightySevenCG_17536447 : Nat.Prime 17536447 := by norm_num

private theorem prime_eightySevenCG_18012793 : Nat.Prime 18012793 := by norm_num

private theorem prime_eightySevenCG_19485097 : Nat.Prime 19485097 := by norm_num

private theorem prime_eightySevenCG_19860481 : Nat.Prime 19860481 := by norm_num

private theorem prime_eightySevenCG_22127701 : Nat.Prime 22127701 := by norm_num

private theorem prime_eightySevenCG_25044269 : Nat.Prime 25044269 := by norm_num

private theorem prime_eightySevenCG_28387663 : Nat.Prime 28387663 := by norm_num

private theorem prime_eightySevenCG_29315603 : Nat.Prime 29315603 := by norm_num

private theorem prime_eightySevenCG_30889267 : Nat.Prime 30889267 := by
  apply lucas_primality 30889267 (2 : ZMod 30889267)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (941, 1), (5471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (941, 1), (5471, 1)] : List FactorBlock).map factorBlockValue).prod) = 30889267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_941
      · exact prime_eightySevenCG_5471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30889267) ^ 15444633 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 30889267) ^ 10296422 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 30889267) ^ 32826 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 30889267) ^ 5646 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_31088923 : Nat.Prime 31088923 := by
  apply lucas_primality 31088923 (2 : ZMod 31088923)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (181, 1), (28627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (181, 1), (28627, 1)] : List FactorBlock).map factorBlockValue).prod) = 31088923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_181
      · exact prime_eightySevenCG_28627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31088923) ^ 15544461 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 31088923) ^ 10362974 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 31088923) ^ 171762 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 31088923) ^ 1086 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_31293329 : Nat.Prime 31293329 := by
  apply lucas_primality 31293329 (3 : ZMod 31293329)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (17, 1), (10459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (17, 1), (10459, 1)] : List FactorBlock).map factorBlockValue).prod) = 31293329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_17
      · exact prime_eightySevenCG_10459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31293329) ^ 15646664 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31293329) ^ 2844848 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31293329) ^ 1840784 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31293329) ^ 2992 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_32313079 : Nat.Prime 32313079 := by
  apply lucas_primality 32313079 (3 : ZMod 32313079)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (317, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (317, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod) = 32313079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_317
      · exact prime_eightySevenCG_809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32313079) ^ 16156539 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 32313079) ^ 10771026 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 32313079) ^ 4616154 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 32313079) ^ 101934 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 32313079) ^ 39942 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_32789357 : Nat.Prime 32789357 := by
  apply lucas_primality 32789357 (2 : ZMod 32789357)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8197339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8197339, 1)] : List FactorBlock).map factorBlockValue).prod) = 32789357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_8197339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 32789357) ^ 16394678 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 32789357) ^ 4 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_36804217 : Nat.Prime 36804217 := by
  apply lucas_primality 36804217 (5 : ZMod 36804217)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (43, 1), (1877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (43, 1), (1877, 1)] : List FactorBlock).map factorBlockValue).prod) = 36804217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_19
      · exact prime_eightySevenCG_43
      · exact prime_eightySevenCG_1877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36804217) ^ 18402108 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36804217) ^ 12268072 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36804217) ^ 1937064 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36804217) ^ 855912 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36804217) ^ 19608 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_37004069 : Nat.Prime 37004069 := by
  apply lucas_primality 37004069 (2 : ZMod 37004069)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9251017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9251017, 1)] : List FactorBlock).map factorBlockValue).prod) = 37004069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_9251017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 37004069) ^ 18502034 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 37004069) ^ 4 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_43532323 : Nat.Prime 43532323 := by
  apply lucas_primality 43532323 (3 : ZMod 43532323)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (233, 1), (31139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (233, 1), (31139, 1)] : List FactorBlock).map factorBlockValue).prod) = 43532323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_233
      · exact prime_eightySevenCG_31139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 43532323) ^ 21766161 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 43532323) ^ 14510774 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 43532323) ^ 186834 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 43532323) ^ 1398 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_44671723 : Nat.Prime 44671723 := by
  apply lucas_primality 44671723 (2 : ZMod 44671723)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7445287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7445287, 1)] : List FactorBlock).map factorBlockValue).prod) = 44671723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7445287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 44671723) ^ 22335861 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44671723) ^ 14890574 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44671723) ^ 6 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_47549279 : Nat.Prime 47549279 := by
  apply lucas_primality 47549279 (7 : ZMod 47549279)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (3396377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (3396377, 1)] : List FactorBlock).map factorBlockValue).prod) = 47549279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_3396377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 47549279) ^ 23774639 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 47549279) ^ 6792754 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 47549279) ^ 14 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_48560741 : Nat.Prime 48560741 := by
  apply lucas_primality 48560741 (2 : ZMod 48560741)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2428037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2428037, 1)] : List FactorBlock).map factorBlockValue).prod) = 48560741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_2428037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 48560741) ^ 24280370 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 48560741) ^ 9712148 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 48560741) ^ 20 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_51315989 : Nat.Prime 51315989 := by
  apply lucas_primality 51315989 (2 : ZMod 51315989)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (12828997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (12828997, 1)] : List FactorBlock).map factorBlockValue).prod) = 51315989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_12828997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 51315989) ^ 25657994 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 51315989) ^ 4 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_52288297 : Nat.Prime 52288297 := by
  apply lucas_primality 52288297 (7 : ZMod 52288297)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2178679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2178679, 1)] : List FactorBlock).map factorBlockValue).prod) = 52288297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_2178679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 52288297) ^ 26144148 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 52288297) ^ 17429432 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 52288297) ^ 24 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_53554663 : Nat.Prime 53554663 := by
  apply lucas_primality 53554663 (6 : ZMod 53554663)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (141679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (141679, 1)] : List FactorBlock).map factorBlockValue).prod) = 53554663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_141679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 53554663) ^ 26777331 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 53554663) ^ 17851554 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 53554663) ^ 7650666 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 53554663) ^ 378 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_57544451 : Nat.Prime 57544451 := by
  apply lucas_primality 57544451 (2 : ZMod 57544451)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (47, 2), (521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (47, 2), (521, 1)] : List FactorBlock).map factorBlockValue).prod) = 57544451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_47
      · exact prime_eightySevenCG_521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57544451) ^ 28772225 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 57544451) ^ 11508890 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 57544451) ^ 1224350 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 57544451) ^ 110450 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_63856399 : Nat.Prime 63856399 := by
  apply lucas_primality 63856399 (3 : ZMod 63856399)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1741, 1), (6113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1741, 1), (6113, 1)] : List FactorBlock).map factorBlockValue).prod) = 63856399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_1741
      · exact prime_eightySevenCG_6113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 63856399) ^ 31928199 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 63856399) ^ 21285466 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 63856399) ^ 36678 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 63856399) ^ 10446 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_64159981 : Nat.Prime 64159981 := by
  apply lucas_primality 64159981 (19 : ZMod 64159981)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (739, 1), (1447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (739, 1), (1447, 1)] : List FactorBlock).map factorBlockValue).prod) = 64159981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_739
      · exact prime_eightySevenCG_1447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 64159981) ^ 32079990 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (19 : ZMod 64159981) ^ 21386660 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (19 : ZMod 64159981) ^ 12831996 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (19 : ZMod 64159981) ^ 86820 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (19 : ZMod 64159981) ^ 44340 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_64906691 : Nat.Prime 64906691 := by
  apply lucas_primality 64906691 (2 : ZMod 64906691)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (41, 1), (6883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (41, 1), (6883, 1)] : List FactorBlock).map factorBlockValue).prod) = 64906691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_23
      · exact prime_eightySevenCG_41
      · exact prime_eightySevenCG_6883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 64906691) ^ 32453345 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 64906691) ^ 12981338 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 64906691) ^ 2822030 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 64906691) ^ 1583090 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 64906691) ^ 9430 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_66021589 : Nat.Prime 66021589 := by
  apply lucas_primality 66021589 (2 : ZMod 66021589)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (227, 1), (2693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (227, 1), (2693, 1)] : List FactorBlock).map factorBlockValue).prod) = 66021589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_227
      · exact prime_eightySevenCG_2693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 66021589) ^ 33010794 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 66021589) ^ 22007196 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 66021589) ^ 290844 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 66021589) ^ 24516 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_69466949 : Nat.Prime 69466949 := by
  apply lucas_primality 69466949 (2 : ZMod 69466949)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (598853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (598853, 1)] : List FactorBlock).map factorBlockValue).prod) = 69466949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_29
      · exact prime_eightySevenCG_598853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 69466949) ^ 34733474 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 69466949) ^ 2395412 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 69466949) ^ 116 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_84060247 : Nat.Prime 84060247 := by
  apply lucas_primality 84060247 (3 : ZMod 84060247)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (191, 1), (73351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (191, 1), (73351, 1)] : List FactorBlock).map factorBlockValue).prod) = 84060247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_191
      · exact prime_eightySevenCG_73351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 84060247) ^ 42030123 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 84060247) ^ 28020082 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 84060247) ^ 440106 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 84060247) ^ 1146 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_84727369 : Nat.Prime 84727369 := by
  apply lucas_primality 84727369 (7 : ZMod 84727369)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (106979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (106979, 1)] : List FactorBlock).map factorBlockValue).prod) = 84727369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_106979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 84727369) ^ 42363684 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 84727369) ^ 28242456 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 84727369) ^ 7702488 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 84727369) ^ 792 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_85225979 : Nat.Prime 85225979 := by
  apply lucas_primality 85225979 (2 : ZMod 85225979)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1223, 1), (34843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1223, 1), (34843, 1)] : List FactorBlock).map factorBlockValue).prod) = 85225979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_1223
      · exact prime_eightySevenCG_34843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 85225979) ^ 42612989 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 85225979) ^ 69686 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 85225979) ^ 2446 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_95241721 : Nat.Prime 95241721 := by
  apply lucas_primality 95241721 (29 : ZMod 95241721)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (113383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (113383, 1)] : List FactorBlock).map factorBlockValue).prod) = 95241721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_113383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 95241721) ^ 47620860 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (29 : ZMod 95241721) ^ 31747240 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (29 : ZMod 95241721) ^ 19048344 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (29 : ZMod 95241721) ^ 13605960 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (29 : ZMod 95241721) ^ 840 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_114283357 : Nat.Prime 114283357 := by
  apply lucas_primality 114283357 (5 : ZMod 114283357)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (865783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (865783, 1)] : List FactorBlock).map factorBlockValue).prod) = 114283357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_865783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 114283357) ^ 57141678 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 114283357) ^ 38094452 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 114283357) ^ 10389396 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 114283357) ^ 132 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_131727109 : Nat.Prime 131727109 := by
  apply lucas_primality 131727109 (2 : ZMod 131727109)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (10977259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (10977259, 1)] : List FactorBlock).map factorBlockValue).prod) = 131727109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_10977259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 131727109) ^ 65863554 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 131727109) ^ 43909036 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 131727109) ^ 12 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_147361237 : Nat.Prime 147361237 := by
  apply lucas_primality 147361237 (5 : ZMod 147361237)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (17, 1), (97, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (17, 1), (97, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 147361237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_17
      · exact prime_eightySevenCG_97
      · exact prime_eightySevenCG_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 147361237) ^ 73680618 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 147361237) ^ 49120412 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 147361237) ^ 13396476 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 147361237) ^ 8668308 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 147361237) ^ 1519188 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 147361237) ^ 217668 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_156775799 : Nat.Prime 156775799 := by
  apply lucas_primality 156775799 (11 : ZMod 156775799)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (2703031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (2703031, 1)] : List FactorBlock).map factorBlockValue).prod) = 156775799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_29
      · exact prime_eightySevenCG_2703031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 156775799) ^ 78387899 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (11 : ZMod 156775799) ^ 5406062 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (11 : ZMod 156775799) ^ 58 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_160583789 : Nat.Prime 160583789 := by
  apply lucas_primality 160583789 (2 : ZMod 160583789)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (1384343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (1384343, 1)] : List FactorBlock).map factorBlockValue).prod) = 160583789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_29
      · exact prime_eightySevenCG_1384343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 160583789) ^ 80291894 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 160583789) ^ 5537372 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 160583789) ^ 116 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_173016439 : Nat.Prime 173016439 := by
  apply lucas_primality 173016439 (6 : ZMod 173016439)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (59, 1), (69821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (59, 1), (69821, 1)] : List FactorBlock).map factorBlockValue).prod) = 173016439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_59
      · exact prime_eightySevenCG_69821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 173016439) ^ 86508219 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 173016439) ^ 57672146 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 173016439) ^ 24716634 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 173016439) ^ 2932482 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 173016439) ^ 2478 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_183166199 : Nat.Prime 183166199 := by
  apply lucas_primality 183166199 (13 : ZMod 183166199)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (73, 1), (23671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (73, 1), (23671, 1)] : List FactorBlock).map factorBlockValue).prod) = 183166199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_53
      · exact prime_eightySevenCG_73
      · exact prime_eightySevenCG_23671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 183166199) ^ 91583099 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 183166199) ^ 3455966 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 183166199) ^ 2509126 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 183166199) ^ 7738 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_191688589 : Nat.Prime 191688589 := by
  apply lucas_primality 191688589 (2 : ZMod 191688589)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 2), (13, 2), (643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 2), (13, 2), (643, 1)] : List FactorBlock).map factorBlockValue).prod) = 191688589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 191688589) ^ 95844294 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 191688589) ^ 63896196 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 191688589) ^ 27384084 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 191688589) ^ 14745276 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 191688589) ^ 298116 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_196736143 : Nat.Prime 196736143 := by
  apply lucas_primality 196736143 (5 : ZMod 196736143)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (32789357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (32789357, 1)] : List FactorBlock).map factorBlockValue).prod) = 196736143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_32789357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 196736143) ^ 98368071 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 196736143) ^ 65578714 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 196736143) ^ 6 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_208550347 : Nat.Prime 208550347 := by
  apply lucas_primality 208550347 (5 : ZMod 208550347)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (1829389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (1829389, 1)] : List FactorBlock).map factorBlockValue).prod) = 208550347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_19
      · exact prime_eightySevenCG_1829389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 208550347) ^ 104275173 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 208550347) ^ 69516782 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 208550347) ^ 10976334 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 208550347) ^ 114 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_220207441 : Nat.Prime 220207441 := by
  apply lucas_primality 220207441 (14 : ZMod 220207441)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (29, 2), (1091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (29, 2), (1091, 1)] : List FactorBlock).map factorBlockValue).prod) = 220207441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_29
      · exact prime_eightySevenCG_1091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 220207441) ^ 110103720 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 220207441) ^ 73402480 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 220207441) ^ 44041488 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 220207441) ^ 7593360 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 220207441) ^ 201840 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_227915081 : Nat.Prime 227915081 := by
  apply lucas_primality 227915081 (6 : ZMod 227915081)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (97, 1), (58741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (97, 1), (58741, 1)] : List FactorBlock).map factorBlockValue).prod) = 227915081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_97
      · exact prime_eightySevenCG_58741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 227915081) ^ 113957540 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 227915081) ^ 45583016 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 227915081) ^ 2349640 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 227915081) ^ 3880 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_230242841 : Nat.Prime 230242841 := by
  apply lucas_primality 230242841 (3 : ZMod 230242841)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (739, 1), (7789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (739, 1), (7789, 1)] : List FactorBlock).map factorBlockValue).prod) = 230242841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_739
      · exact prime_eightySevenCG_7789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 230242841) ^ 115121420 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 230242841) ^ 46048568 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 230242841) ^ 311560 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 230242841) ^ 29560 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_243474353 : Nat.Prime 243474353 := by
  apply lucas_primality 243474353 (3 : ZMod 243474353)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (1383377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (1383377, 1)] : List FactorBlock).map factorBlockValue).prod) = 243474353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_1383377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 243474353) ^ 121737176 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 243474353) ^ 22134032 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 243474353) ^ 176 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_247644847 : Nat.Prime 247644847 := by
  apply lucas_primality 247644847 (3 : ZMod 247644847)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (521, 1), (26407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (521, 1), (26407, 1)] : List FactorBlock).map factorBlockValue).prod) = 247644847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_521
      · exact prime_eightySevenCG_26407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 247644847) ^ 123822423 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 247644847) ^ 82548282 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 247644847) ^ 475326 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 247644847) ^ 9378 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_268020163 : Nat.Prime 268020163 := by
  apply lucas_primality 268020163 (3 : ZMod 268020163)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1559, 1), (9551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1559, 1), (9551, 1)] : List FactorBlock).map factorBlockValue).prod) = 268020163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_1559
      · exact prime_eightySevenCG_9551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 268020163) ^ 134010081 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 268020163) ^ 89340054 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 268020163) ^ 171918 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 268020163) ^ 28062 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_271652533 : Nat.Prime 271652533 := by
  apply lucas_primality 271652533 (2 : ZMod 271652533)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (71, 1), (318841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (71, 1), (318841, 1)] : List FactorBlock).map factorBlockValue).prod) = 271652533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_71
      · exact prime_eightySevenCG_318841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 271652533) ^ 135826266 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 271652533) ^ 90550844 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 271652533) ^ 3826092 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 271652533) ^ 852 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_279499769 : Nat.Prime 279499769 := by
  apply lucas_primality 279499769 (3 : ZMod 279499769)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (433, 1), (80687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (433, 1), (80687, 1)] : List FactorBlock).map factorBlockValue).prod) = 279499769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_433
      · exact prime_eightySevenCG_80687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 279499769) ^ 139749884 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 279499769) ^ 645496 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 279499769) ^ 3464 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_291840671 : Nat.Prime 291840671 := by
  apply lucas_primality 291840671 (11 : ZMod 291840671)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (2653097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (2653097, 1)] : List FactorBlock).map factorBlockValue).prod) = 291840671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_2653097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 291840671) ^ 145920335 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (11 : ZMod 291840671) ^ 58368134 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (11 : ZMod 291840671) ^ 26530970 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (11 : ZMod 291840671) ^ 110 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_297041923 : Nat.Prime 297041923 := by
  apply lucas_primality 297041923 (2 : ZMod 297041923)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2473, 1), (6673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2473, 1), (6673, 1)] : List FactorBlock).map factorBlockValue).prod) = 297041923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_2473
      · exact prime_eightySevenCG_6673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 297041923) ^ 148520961 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 297041923) ^ 99013974 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 297041923) ^ 120114 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 297041923) ^ 44514 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_341131121 : Nat.Prime 341131121 := by
  apply lucas_primality 341131121 (3 : ZMod 341131121)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 1), (37, 1), (10477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 1), (37, 1), (10477, 1)] : List FactorBlock).map factorBlockValue).prod) = 341131121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_37
      · exact prime_eightySevenCG_10477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 341131121) ^ 170565560 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 341131121) ^ 68226224 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 341131121) ^ 31011920 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 341131121) ^ 9219760 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 341131121) ^ 32560 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_346726979 : Nat.Prime 346726979 := by
  apply lucas_primality 346726979 (6 : ZMod 346726979)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (569, 1), (1019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (569, 1), (1019, 1)] : List FactorBlock).map factorBlockValue).prod) = 346726979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_23
      · exact prime_eightySevenCG_569
      · exact prime_eightySevenCG_1019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 346726979) ^ 173363489 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 346726979) ^ 26671306 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 346726979) ^ 15075086 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 346726979) ^ 609362 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 346726979) ^ 340262 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_398655689 : Nat.Prime 398655689 := by
  apply lucas_primality 398655689 (3 : ZMod 398655689)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (2166607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (2166607, 1)] : List FactorBlock).map factorBlockValue).prod) = 398655689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_23
      · exact prime_eightySevenCG_2166607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 398655689) ^ 199327844 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 398655689) ^ 17332856 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 398655689) ^ 184 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_404781989 : Nat.Prime 404781989 := by
  apply lucas_primality 404781989 (2 : ZMod 404781989)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (53, 1), (193, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (53, 1), (193, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) = 404781989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_53
      · exact prime_eightySevenCG_193
      · exact prime_eightySevenCG_761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 404781989) ^ 202390994 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 404781989) ^ 31137076 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 404781989) ^ 7637396 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 404781989) ^ 2097316 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 404781989) ^ 531908 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_454194859 : Nat.Prime 454194859 := by
  apply lucas_primality 454194859 (2 : ZMod 454194859)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (79, 1), (73709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (79, 1), (73709, 1)] : List FactorBlock).map factorBlockValue).prod) = 454194859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_79
      · exact prime_eightySevenCG_73709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 454194859) ^ 227097429 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 454194859) ^ 151398286 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 454194859) ^ 34938066 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 454194859) ^ 5749302 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 454194859) ^ 6162 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_486100663 : Nat.Prime 486100663 := by
  apply lucas_primality 486100663 (3 : ZMod 486100663)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (683, 1), (118619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (683, 1), (118619, 1)] : List FactorBlock).map factorBlockValue).prod) = 486100663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_683
      · exact prime_eightySevenCG_118619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 486100663) ^ 243050331 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 486100663) ^ 162033554 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 486100663) ^ 711714 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 486100663) ^ 4098 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_524811929 : Nat.Prime 524811929 := by
  apply lucas_primality 524811929 (3 : ZMod 524811929)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (137, 1), (478843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (137, 1), (478843, 1)] : List FactorBlock).map factorBlockValue).prod) = 524811929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_137
      · exact prime_eightySevenCG_478843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 524811929) ^ 262405964 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 524811929) ^ 3830744 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 524811929) ^ 1096 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_537343399 : Nat.Prime 537343399 := by
  apply lucas_primality 537343399 (3 : ZMod 537343399)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (131, 1), (7351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (131, 1), (7351, 1)] : List FactorBlock).map factorBlockValue).prod) = 537343399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_31
      · exact prime_eightySevenCG_131
      · exact prime_eightySevenCG_7351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 537343399) ^ 268671699 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 537343399) ^ 179114466 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 537343399) ^ 17333658 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 537343399) ^ 4101858 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 537343399) ^ 73098 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_543924211 : Nat.Prime 543924211 := by
  apply lucas_primality 543924211 (2 : ZMod 543924211)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (954253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (954253, 1)] : List FactorBlock).map factorBlockValue).prod) = 543924211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_19
      · exact prime_eightySevenCG_954253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 543924211) ^ 271962105 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 543924211) ^ 181308070 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 543924211) ^ 108784842 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 543924211) ^ 28627590 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 543924211) ^ 570 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_580219021 : Nat.Prime 580219021 := by
  apply lucas_primality 580219021 (2 : ZMod 580219021)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (3223439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (3223439, 1)] : List FactorBlock).map factorBlockValue).prod) = 580219021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_3223439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 580219021) ^ 290109510 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 580219021) ^ 193406340 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 580219021) ^ 116043804 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 580219021) ^ 180 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_586312061 : Nat.Prime 586312061 := by
  apply lucas_primality 586312061 (3 : ZMod 586312061)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29315603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29315603, 1)] : List FactorBlock).map factorBlockValue).prod) = 586312061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_29315603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 586312061) ^ 293156030 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 586312061) ^ 117262412 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 586312061) ^ 20 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_589444949 : Nat.Prime 589444949 := by
  apply lucas_primality 589444949 (2 : ZMod 589444949)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (147361237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (147361237, 1)] : List FactorBlock).map factorBlockValue).prod) = 589444949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_147361237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 589444949) ^ 294722474 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 589444949) ^ 4 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_611943907 : Nat.Prime 611943907 := by
  apply lucas_primality 611943907 (3 : ZMod 611943907)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (29, 1), (31, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (29, 1), (31, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) = 611943907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_19
      · exact prime_eightySevenCG_29
      · exact prime_eightySevenCG_31
      · exact prime_eightySevenCG_853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 611943907) ^ 305971953 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 611943907) ^ 203981302 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 611943907) ^ 87420558 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 611943907) ^ 32207574 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 611943907) ^ 21101514 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 611943907) ^ 19740126 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 611943907) ^ 717402 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_613777319 : Nat.Prime 613777319 := by
  apply lucas_primality 613777319 (7 : ZMod 613777319)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (3985567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (3985567, 1)] : List FactorBlock).map factorBlockValue).prod) = 613777319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_3985567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 613777319) ^ 306888659 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 613777319) ^ 87682474 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 613777319) ^ 55797938 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 613777319) ^ 154 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_641866553 : Nat.Prime 641866553 := by
  apply lucas_primality 641866553 (3 : ZMod 641866553)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (4719607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (4719607, 1)] : List FactorBlock).map factorBlockValue).prod) = 641866553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_17
      · exact prime_eightySevenCG_4719607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 641866553) ^ 320933276 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 641866553) ^ 37756856 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 641866553) ^ 136 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_710088923 : Nat.Prime 710088923 := by
  apply lucas_primality 710088923 (2 : ZMod 710088923)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (61, 1), (141961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (61, 1), (141961, 1)] : List FactorBlock).map factorBlockValue).prod) = 710088923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_41
      · exact prime_eightySevenCG_61
      · exact prime_eightySevenCG_141961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 710088923) ^ 355044461 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 710088923) ^ 17319242 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 710088923) ^ 11640802 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 710088923) ^ 5002 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_766754357 : Nat.Prime 766754357 := by
  apply lucas_primality 766754357 (2 : ZMod 766754357)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191688589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191688589, 1)] : List FactorBlock).map factorBlockValue).prod) = 766754357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_191688589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 766754357) ^ 383377178 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 766754357) ^ 4 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_806371541 : Nat.Prime 806371541 := by
  apply lucas_primality 806371541 (3 : ZMod 806371541)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (17, 1), (241, 1), (757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (17, 1), (241, 1), (757, 1)] : List FactorBlock).map factorBlockValue).prod) = 806371541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_17
      · exact prime_eightySevenCG_241
      · exact prime_eightySevenCG_757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 806371541) ^ 403185770 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 806371541) ^ 161274308 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 806371541) ^ 62028580 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 806371541) ^ 47433620 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 806371541) ^ 3345940 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 806371541) ^ 1065220 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_907214881 : Nat.Prime 907214881 := by
  apply lucas_primality 907214881 (14 : ZMod 907214881)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (11, 1), (13, 1), (13217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (11, 1), (13, 1), (13217, 1)] : List FactorBlock).map factorBlockValue).prod) = 907214881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_13217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 907214881) ^ 453607440 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 907214881) ^ 302404960 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 907214881) ^ 181442976 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 907214881) ^ 82474080 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 907214881) ^ 69785760 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 907214881) ^ 68640 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_995807789 : Nat.Prime 995807789 := by
  apply lucas_primality 995807789 (2 : ZMod 995807789)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (179, 1), (37589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (179, 1), (37589, 1)] : List FactorBlock).map factorBlockValue).prod) = 995807789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_37
      · exact prime_eightySevenCG_179
      · exact prime_eightySevenCG_37589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 995807789) ^ 497903894 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 995807789) ^ 26913724 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 995807789) ^ 5563172 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 995807789) ^ 26492 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1073660377 : Nat.Prime 1073660377 := by
  apply lucas_primality 1073660377 (10 : ZMod 1073660377)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (499, 1), (2423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (499, 1), (2423, 1)] : List FactorBlock).map factorBlockValue).prod) = 1073660377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_37
      · exact prime_eightySevenCG_499
      · exact prime_eightySevenCG_2423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1073660377) ^ 536830188 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1073660377) ^ 357886792 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1073660377) ^ 29017848 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1073660377) ^ 2151624 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1073660377) ^ 443112 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1180416859 : Nat.Prime 1180416859 := by
  apply lucas_primality 1180416859 (13 : ZMod 1180416859)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (196736143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (196736143, 1)] : List FactorBlock).map factorBlockValue).prod) = 1180416859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_196736143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 1180416859) ^ 590208429 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 1180416859) ^ 393472286 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 1180416859) ^ 6 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1247981699 : Nat.Prime 1247981699 := by
  apply lucas_primality 1247981699 (2 : ZMod 1247981699)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (683, 1), (22283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (683, 1), (22283, 1)] : List FactorBlock).map factorBlockValue).prod) = 1247981699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_41
      · exact prime_eightySevenCG_683
      · exact prime_eightySevenCG_22283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1247981699) ^ 623990849 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1247981699) ^ 30438578 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1247981699) ^ 1827206 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1247981699) ^ 56006 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1248126881 : Nat.Prime 1248126881 := by
  apply lucas_primality 1248126881 (3 : ZMod 1248126881)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 1), (11, 1), (13, 1), (7793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 1), (11, 1), (13, 1), (7793, 1)] : List FactorBlock).map factorBlockValue).prod) = 1248126881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_7793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1248126881) ^ 624063440 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1248126881) ^ 249625376 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1248126881) ^ 178303840 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1248126881) ^ 113466080 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1248126881) ^ 96009760 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1248126881) ^ 160160 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1452569653 : Nat.Prime 1452569653 := by
  apply lucas_primality 1452569653 (2 : ZMod 1452569653)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (157, 1), (85667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (157, 1), (85667, 1)] : List FactorBlock).map factorBlockValue).prod) = 1452569653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_157
      · exact prime_eightySevenCG_85667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1452569653) ^ 726284826 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1452569653) ^ 484189884 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1452569653) ^ 9252036 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1452569653) ^ 16956 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1523867537 : Nat.Prime 1523867537 := by
  apply lucas_primality 1523867537 (3 : ZMod 1523867537)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (95241721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (95241721, 1)] : List FactorBlock).map factorBlockValue).prod) = 1523867537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_95241721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1523867537) ^ 761933768 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1523867537) ^ 16 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1613358511 : Nat.Prime 1613358511 := by
  apply lucas_primality 1613358511 (6 : ZMod 1613358511)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (701, 1), (76717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (701, 1), (76717, 1)] : List FactorBlock).map factorBlockValue).prod) = 1613358511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_701
      · exact prime_eightySevenCG_76717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1613358511) ^ 806679255 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1613358511) ^ 537786170 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1613358511) ^ 322671702 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1613358511) ^ 2301510 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1613358511) ^ 21030 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1991615579 : Nat.Prime 1991615579 := by
  apply lucas_primality 1991615579 (2 : ZMod 1991615579)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (995807789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (995807789, 1)] : List FactorBlock).map factorBlockValue).prod) = 1991615579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_995807789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1991615579) ^ 995807789 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1991615579) ^ 2 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_2282791529 : Nat.Prime 2282791529 := by
  apply lucas_primality 2282791529 (3 : ZMod 2282791529)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (163, 1), (1750607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (163, 1), (1750607, 1)] : List FactorBlock).map factorBlockValue).prod) = 2282791529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_163
      · exact prime_eightySevenCG_1750607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2282791529) ^ 1141395764 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2282791529) ^ 14004856 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2282791529) ^ 1304 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_2288448391 : Nat.Prime 2288448391 := by
  apply lucas_primality 2288448391 (3 : ZMod 2288448391)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (43, 1), (1193, 1), (1487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (43, 1), (1193, 1), (1487, 1)] : List FactorBlock).map factorBlockValue).prod) = 2288448391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_43
      · exact prime_eightySevenCG_1193
      · exact prime_eightySevenCG_1487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2288448391) ^ 1144224195 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2288448391) ^ 762816130 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2288448391) ^ 457689678 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2288448391) ^ 53219730 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2288448391) ^ 1918230 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2288448391) ^ 1538970 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_2417840927 : Nat.Prime 2417840927 := by
  apply lucas_primality 2417840927 (5 : ZMod 2417840927)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (3547, 1), (5087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (3547, 1), (5087, 1)] : List FactorBlock).map factorBlockValue).prod) = 2417840927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_67
      · exact prime_eightySevenCG_3547
      · exact prime_eightySevenCG_5087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2417840927) ^ 1208920463 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2417840927) ^ 36087178 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2417840927) ^ 681658 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2417840927) ^ 475298 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_2551650701 : Nat.Prime 2551650701 := by
  apply lucas_primality 2551650701 (3 : ZMod 2551650701)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (17, 1), (839, 1), (1789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (17, 1), (839, 1), (1789, 1)] : List FactorBlock).map factorBlockValue).prod) = 2551650701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_17
      · exact prime_eightySevenCG_839
      · exact prime_eightySevenCG_1789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2551650701) ^ 1275825350 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2551650701) ^ 510330140 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2551650701) ^ 150097100 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2551650701) ^ 3041300 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2551650701) ^ 1426300 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_2618426137 : Nat.Prime 2618426137 := by
  apply lucas_primality 2618426137 (7 : ZMod 2618426137)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (59, 1), (1849171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (59, 1), (1849171, 1)] : List FactorBlock).map factorBlockValue).prod) = 2618426137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_59
      · exact prime_eightySevenCG_1849171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2618426137) ^ 1309213068 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 2618426137) ^ 872808712 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 2618426137) ^ 44380104 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 2618426137) ^ 1416 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_3183468787 : Nat.Prime 3183468787 := by
  apply lucas_primality 3183468787 (2 : ZMod 3183468787)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (691, 1), (255947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (691, 1), (255947, 1)] : List FactorBlock).map factorBlockValue).prod) = 3183468787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_691
      · exact prime_eightySevenCG_255947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3183468787) ^ 1591734393 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3183468787) ^ 1061156262 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3183468787) ^ 4607046 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3183468787) ^ 12438 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_3408640943 : Nat.Prime 3408640943 := by
  apply lucas_primality 3408640943 (5 : ZMod 3408640943)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (243474353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (243474353, 1)] : List FactorBlock).map factorBlockValue).prod) = 3408640943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_243474353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3408640943) ^ 1704320471 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3408640943) ^ 486948706 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3408640943) ^ 14 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_3696447437 : Nat.Prime 3696447437 := by
  apply lucas_primality 3696447437 (2 : ZMod 3696447437)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (131, 1), (641299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (131, 1), (641299, 1)] : List FactorBlock).map factorBlockValue).prod) = 3696447437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_131
      · exact prime_eightySevenCG_641299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3696447437) ^ 1848223718 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3696447437) ^ 336040676 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3696447437) ^ 28217156 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3696447437) ^ 5764 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_3983231159 : Nat.Prime 3983231159 := by
  apply lucas_primality 3983231159 (13 : ZMod 3983231159)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1991615579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1991615579, 1)] : List FactorBlock).map factorBlockValue).prod) = 3983231159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_1991615579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 3983231159) ^ 1991615579 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 3983231159) ^ 2 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_4113753337 : Nat.Prime 4113753337 := by
  apply lucas_primality 4113753337 (5 : ZMod 4113753337)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (11, 1), (307, 1), (2417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (11, 1), (307, 1), (2417, 1)] : List FactorBlock).map factorBlockValue).prod) = 4113753337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_307
      · exact prime_eightySevenCG_2417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4113753337) ^ 2056876668 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4113753337) ^ 1371251112 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4113753337) ^ 587679048 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4113753337) ^ 373977576 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4113753337) ^ 13399848 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4113753337) ^ 1702008 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_4506239377 : Nat.Prime 4506239377 := by
  apply lucas_primality 4506239377 (5 : ZMod 4506239377)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (31293329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (31293329, 1)] : List FactorBlock).map factorBlockValue).prod) = 4506239377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_31293329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4506239377) ^ 2253119688 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4506239377) ^ 1502079792 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4506239377) ^ 144 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_4571334281 : Nat.Prime 4571334281 := by
  apply lucas_primality 4571334281 (3 : ZMod 4571334281)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (114283357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (114283357, 1)] : List FactorBlock).map factorBlockValue).prod) = 4571334281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_114283357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4571334281) ^ 2285667140 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4571334281) ^ 914266856 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4571334281) ^ 40 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_4600526143 : Nat.Prime 4600526143 := by
  apply lucas_primality 4600526143 (3 : ZMod 4600526143)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (766754357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (766754357, 1)] : List FactorBlock).map factorBlockValue).prod) = 4600526143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_766754357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4600526143) ^ 2300263071 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4600526143) ^ 1533508714 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4600526143) ^ 6 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_4665475621 : Nat.Prime 4665475621 := by
  apply lucas_primality 4665475621 (2 : ZMod 4665475621)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (13, 1), (241, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (13, 1), (241, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 4665475621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_241
      · exact prime_eightySevenCG_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4665475621) ^ 2332737810 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4665475621) ^ 1555158540 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4665475621) ^ 933095124 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4665475621) ^ 358882740 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4665475621) ^ 19358820 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4665475621) ^ 563940 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_5103301403 : Nat.Prime 5103301403 := by
  apply lucas_primality 5103301403 (2 : ZMod 5103301403)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2551650701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2551650701, 1)] : List FactorBlock).map factorBlockValue).prod) = 5103301403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_2551650701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5103301403) ^ 2551650701 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5103301403) ^ 2 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_5433724573 : Nat.Prime 5433724573 := by
  apply lucas_primality 5433724573 (5 : ZMod 5433724573)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (61, 1), (71, 1), (104551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (61, 1), (71, 1), (104551, 1)] : List FactorBlock).map factorBlockValue).prod) = 5433724573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_61
      · exact prime_eightySevenCG_71
      · exact prime_eightySevenCG_104551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5433724573) ^ 2716862286 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5433724573) ^ 1811241524 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5433724573) ^ 89077452 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5433724573) ^ 76531332 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5433724573) ^ 51972 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_5926155637 : Nat.Prime 5926155637 := by
  apply lucas_primality 5926155637 (5 : ZMod 5926155637)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (97, 1), (5091199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (97, 1), (5091199, 1)] : List FactorBlock).map factorBlockValue).prod) = 5926155637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_97
      · exact prime_eightySevenCG_5091199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5926155637) ^ 2963077818 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5926155637) ^ 1975385212 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5926155637) ^ 61094388 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5926155637) ^ 1164 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_7113263887 : Nat.Prime 7113263887 := by
  apply lucas_primality 7113263887 (5 : ZMod 7113263887)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (131727109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (131727109, 1)] : List FactorBlock).map factorBlockValue).prod) = 7113263887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_131727109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7113263887) ^ 3556631943 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 7113263887) ^ 2371087962 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 7113263887) ^ 54 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_8179822507 : Nat.Prime 8179822507 := by
  apply lucas_primality 8179822507 (3 : ZMod 8179822507)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (41, 1), (1750069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (41, 1), (1750069, 1)] : List FactorBlock).map factorBlockValue).prod) = 8179822507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_19
      · exact prime_eightySevenCG_41
      · exact prime_eightySevenCG_1750069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8179822507) ^ 4089911253 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8179822507) ^ 2726607502 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8179822507) ^ 430516974 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8179822507) ^ 199507866 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8179822507) ^ 4674 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_9734540191 : Nat.Prime 9734540191 := by
  apply lucas_primality 9734540191 (3 : ZMod 9734540191)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (181, 1), (859, 1), (2087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (181, 1), (859, 1), (2087, 1)] : List FactorBlock).map factorBlockValue).prod) = 9734540191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_181
      · exact prime_eightySevenCG_859
      · exact prime_eightySevenCG_2087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9734540191) ^ 4867270095 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9734540191) ^ 3244846730 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9734540191) ^ 1946908038 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9734540191) ^ 53781990 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9734540191) ^ 11332410 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9734540191) ^ 4664370 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_11649639971 : Nat.Prime 11649639971 := by
  apply lucas_primality 11649639971 (2 : ZMod 11649639971)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (101, 1), (307, 1), (37571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (101, 1), (307, 1), (37571, 1)] : List FactorBlock).map factorBlockValue).prod) = 11649639971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_101
      · exact prime_eightySevenCG_307
      · exact prime_eightySevenCG_37571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11649639971) ^ 5824819985 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11649639971) ^ 2329927994 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11649639971) ^ 115342970 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11649639971) ^ 37946710 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11649639971) ^ 310070 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_12535721053 : Nat.Prime 12535721053 := by
  apply lucas_primality 12535721053 (2 : ZMod 12535721053)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (599, 1), (102587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (599, 1), (102587, 1)] : List FactorBlock).map factorBlockValue).prod) = 12535721053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_17
      · exact prime_eightySevenCG_599
      · exact prime_eightySevenCG_102587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12535721053) ^ 6267860526 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12535721053) ^ 4178573684 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12535721053) ^ 737395356 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12535721053) ^ 20927748 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12535721053) ^ 122196 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_16040263843 : Nat.Prime 16040263843 := by
  apply lucas_primality 16040263843 (3 : ZMod 16040263843)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (297041923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (297041923, 1)] : List FactorBlock).map factorBlockValue).prod) = 16040263843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_297041923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 16040263843) ^ 8020131921 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 16040263843) ^ 5346754614 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 16040263843) ^ 54 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_21482384927 : Nat.Prime 21482384927 := by
  apply lucas_primality 21482384927 (5 : ZMod 21482384927)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (37, 1), (10010431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (37, 1), (10010431, 1)] : List FactorBlock).map factorBlockValue).prod) = 21482384927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_29
      · exact prime_eightySevenCG_37
      · exact prime_eightySevenCG_10010431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 21482384927) ^ 10741192463 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 21482384927) ^ 740771894 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 21482384927) ^ 580604998 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 21482384927) ^ 2146 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_22178684623 : Nat.Prime 22178684623 := by
  apply lucas_primality 22178684623 (3 : ZMod 22178684623)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3696447437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3696447437, 1)] : List FactorBlock).map factorBlockValue).prod) = 22178684623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_3696447437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 22178684623) ^ 11089342311 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 22178684623) ^ 7392894874 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 22178684623) ^ 6 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_23131577101 : Nat.Prime 23131577101 := by
  apply lucas_primality 23131577101 (2 : ZMod 23131577101)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (83, 1), (928979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (83, 1), (928979, 1)] : List FactorBlock).map factorBlockValue).prod) = 23131577101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_83
      · exact prime_eightySevenCG_928979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23131577101) ^ 11565788550 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 23131577101) ^ 7710525700 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 23131577101) ^ 4626315420 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 23131577101) ^ 278693700 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 23131577101) ^ 24900 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_24006435329 : Nat.Prime 24006435329 := by
  apply lucas_primality 24006435329 (3 : ZMod 24006435329)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (97, 1), (483377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (97, 1), (483377, 1)] : List FactorBlock).map factorBlockValue).prod) = 24006435329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_97
      · exact prime_eightySevenCG_483377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 24006435329) ^ 12003217664 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 24006435329) ^ 247489024 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 24006435329) ^ 49664 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_24369198883 : Nat.Prime 24369198883 := by
  apply lucas_primality 24369198883 (2 : ZMod 24369198883)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (580219021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (580219021, 1)] : List FactorBlock).map factorBlockValue).prod) = 24369198883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_580219021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24369198883) ^ 12184599441 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 24369198883) ^ 8123066294 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 24369198883) ^ 3481314126 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 24369198883) ^ 42 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_28069209437 : Nat.Prime 28069209437 := by
  apply lucas_primality 28069209437 (2 : ZMod 28069209437)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37493, 1), (187163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37493, 1), (187163, 1)] : List FactorBlock).map factorBlockValue).prod) = 28069209437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_37493
      · exact prime_eightySevenCG_187163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 28069209437) ^ 14034604718 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 28069209437) ^ 748652 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 28069209437) ^ 149972 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_31674465209 : Nat.Prime 31674465209 := by
  apply lucas_primality 31674465209 (3 : ZMod 31674465209)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (64906691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (64906691, 1)] : List FactorBlock).map factorBlockValue).prod) = 31674465209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_61
      · exact prime_eightySevenCG_64906691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 31674465209) ^ 15837232604 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31674465209) ^ 519253528 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31674465209) ^ 488 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_35165115851 : Nat.Prime 35165115851 := by
  apply lucas_primality 35165115851 (2 : ZMod 35165115851)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (373, 1), (1885529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (373, 1), (1885529, 1)] : List FactorBlock).map factorBlockValue).prod) = 35165115851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_373
      · exact prime_eightySevenCG_1885529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35165115851) ^ 17582557925 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 35165115851) ^ 7033023170 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 35165115851) ^ 94276450 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 35165115851) ^ 18650 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_44156009363 : Nat.Prime 44156009363 := by
  apply lucas_primality 44156009363 (2 : ZMod 44156009363)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (257, 1), (977, 1), (3823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (257, 1), (977, 1), (3823, 1)] : List FactorBlock).map factorBlockValue).prod) = 44156009363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_23
      · exact prime_eightySevenCG_257
      · exact prime_eightySevenCG_977
      · exact prime_eightySevenCG_3823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44156009363) ^ 22078004681 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44156009363) ^ 1919826494 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44156009363) ^ 171813266 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44156009363) ^ 45195506 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44156009363) ^ 11550094 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_47874630883 : Nat.Prime 47874630883 := by
  apply lucas_primality 47874630883 (2 : ZMod 47874630883)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (613777319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (613777319, 1)] : List FactorBlock).map factorBlockValue).prod) = 47874630883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_613777319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47874630883) ^ 23937315441 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 47874630883) ^ 15958210294 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 47874630883) ^ 3682663914 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 47874630883) ^ 78 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_53274821689 : Nat.Prime 53274821689 := by
  apply lucas_primality 53274821689 (7 : ZMod 53274821689)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (11, 1), (109, 1), (191, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (11, 1), (109, 1), (191, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) = 53274821689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_109
      · exact prime_eightySevenCG_191
      · exact prime_eightySevenCG_359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 53274821689) ^ 26637410844 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 53274821689) ^ 17758273896 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 53274821689) ^ 4843165608 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 53274821689) ^ 488759832 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 53274821689) ^ 278925768 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 53274821689) ^ 148397832 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_64161055373 : Nat.Prime 64161055373 := by
  apply lucas_primality 64161055373 (2 : ZMod 64161055373)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (16040263843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (16040263843, 1)] : List FactorBlock).map factorBlockValue).prod) = 64161055373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_16040263843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 64161055373) ^ 32080527686 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 64161055373) ^ 4 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_65468239583 : Nat.Prime 65468239583 := by
  apply lucas_primality 65468239583 (5 : ZMod 65468239583)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1871, 1), (17495521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1871, 1), (17495521, 1)] : List FactorBlock).map factorBlockValue).prod) = 65468239583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_1871
      · exact prime_eightySevenCG_17495521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 65468239583) ^ 32734119791 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 65468239583) ^ 34991042 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 65468239583) ^ 3742 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_65820053393 : Nat.Prime 65820053393 := by
  apply lucas_primality 65820053393 (3 : ZMod 65820053393)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (4113753337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (4113753337, 1)] : List FactorBlock).map factorBlockValue).prod) = 65820053393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_4113753337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 65820053393) ^ 32910026696 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 65820053393) ^ 16 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_82284017059 : Nat.Prime 82284017059 := by
  apply lucas_primality 82284017059 (2 : ZMod 82284017059)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4571334281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4571334281, 1)] : List FactorBlock).map factorBlockValue).prod) = 82284017059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_4571334281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 82284017059) ^ 41142008529 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 82284017059) ^ 27428005686 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 82284017059) ^ 18 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_82522292861 : Nat.Prime 82522292861 := by
  apply lucas_primality 82522292861 (3 : ZMod 82522292861)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (589444949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (589444949, 1)] : List FactorBlock).map factorBlockValue).prod) = 82522292861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_589444949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 82522292861) ^ 41261146430 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 82522292861) ^ 16504458572 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 82522292861) ^ 11788898980 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 82522292861) ^ 140 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_95434409467 : Nat.Prime 95434409467 := by
  apply lucas_primality 95434409467 (3 : ZMod 95434409467)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (11, 1), (53554663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (11, 1), (53554663, 1)] : List FactorBlock).map factorBlockValue).prod) = 95434409467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_53554663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 95434409467) ^ 47717204733 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 95434409467) ^ 31811469822 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 95434409467) ^ 8675855406 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 95434409467) ^ 1782 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_95994553631 : Nat.Prime 95994553631 := by
  apply lucas_primality 95994553631 (7 : ZMod 95994553631)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (21319, 1), (450277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (21319, 1), (450277, 1)] : List FactorBlock).map factorBlockValue).prod) = 95994553631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_21319
      · exact prime_eightySevenCG_450277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 95994553631) ^ 47997276815 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 95994553631) ^ 19198910726 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 95994553631) ^ 4502770 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 95994553631) ^ 213190 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_119938678267 : Nat.Prime 119938678267 := by
  apply lucas_primality 119938678267 (5 : ZMod 119938678267)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (19, 2), (23, 1), (101, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (19, 2), (23, 1), (101, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod) = 119938678267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_19
      · exact prime_eightySevenCG_23
      · exact prime_eightySevenCG_101
      · exact prime_eightySevenCG_197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 119938678267) ^ 59969339133 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 119938678267) ^ 39979559422 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 119938678267) ^ 10903516206 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 119938678267) ^ 6312562014 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 119938678267) ^ 5214725142 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 119938678267) ^ 1187511666 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 119938678267) ^ 608825778 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_144572738201 : Nat.Prime 144572738201 := by
  apply lucas_primality 144572738201 (3 : ZMod 144572738201)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (11, 1), (97, 1), (677473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (11, 1), (97, 1), (677473, 1)] : List FactorBlock).map factorBlockValue).prod) = 144572738201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_97
      · exact prime_eightySevenCG_677473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 144572738201) ^ 72286369100 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 144572738201) ^ 28914547640 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 144572738201) ^ 13142976200 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 144572738201) ^ 1490440600 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 144572738201) ^ 213400 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_173282436553 : Nat.Prime 173282436553 := by
  apply lucas_primality 173282436553 (5 : ZMod 173282436553)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (347, 1), (562357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (347, 1), (562357, 1)] : List FactorBlock).map factorBlockValue).prod) = 173282436553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_37
      · exact prime_eightySevenCG_347
      · exact prime_eightySevenCG_562357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 173282436553) ^ 86641218276 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 173282436553) ^ 57760812184 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 173282436553) ^ 4683309096 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 173282436553) ^ 499373016 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 173282436553) ^ 308136 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_179354380129 : Nat.Prime 179354380129 := by
  apply lucas_primality 179354380129 (13 : ZMod 179354380129)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 2), (11, 1), (43, 1), (149, 1), (541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 2), (11, 1), (43, 1), (149, 1), (541, 1)] : List FactorBlock).map factorBlockValue).prod) = 179354380129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_43
      · exact prime_eightySevenCG_149
      · exact prime_eightySevenCG_541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 179354380129) ^ 89677190064 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 179354380129) ^ 59784793376 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 179354380129) ^ 25622054304 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 179354380129) ^ 16304943648 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 179354380129) ^ 4171032096 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 179354380129) ^ 1203720672 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 179354380129) ^ 331523808 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_213336896953 : Nat.Prime 213336896953 := by
  apply lucas_primality 213336896953 (10 : ZMod 213336896953)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (541, 1), (641, 1), (25633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (541, 1), (641, 1), (25633, 1)] : List FactorBlock).map factorBlockValue).prod) = 213336896953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_541
      · exact prime_eightySevenCG_641
      · exact prime_eightySevenCG_25633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 213336896953) ^ 106668448476 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 213336896953) ^ 71112298984 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 213336896953) ^ 394338072 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 213336896953) ^ 332818872 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 213336896953) ^ 8322744 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_230915814949 : Nat.Prime 230915814949 := by
  apply lucas_primality 230915814949 (2 : ZMod 230915814949)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 2), (13, 1), (59, 1), (103, 1), (1657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 2), (13, 1), (59, 1), (103, 1), (1657, 1)] : List FactorBlock).map factorBlockValue).prod) = 230915814949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_59
      · exact prime_eightySevenCG_103
      · exact prime_eightySevenCG_1657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 230915814949) ^ 115457907474 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 230915814949) ^ 76971938316 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 230915814949) ^ 32987973564 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 230915814949) ^ 17762754996 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 230915814949) ^ 3913827372 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 230915814949) ^ 2241901116 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 230915814949) ^ 139357764 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_356876403551 : Nat.Prime 356876403551 := by
  apply lucas_primality 356876403551 (13 : ZMod 356876403551)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (31, 1), (230242841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (31, 1), (230242841, 1)] : List FactorBlock).map factorBlockValue).prod) = 356876403551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_31
      · exact prime_eightySevenCG_230242841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 356876403551) ^ 178438201775 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 356876403551) ^ 71375280710 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 356876403551) ^ 11512142050 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 356876403551) ^ 1550 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_366457266629 : Nat.Prime 366457266629 := by
  apply lucas_primality 366457266629 (2 : ZMod 366457266629)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (3983231159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (3983231159, 1)] : List FactorBlock).map factorBlockValue).prod) = 366457266629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_23
      · exact prime_eightySevenCG_3983231159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 366457266629) ^ 183228633314 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 366457266629) ^ 15932924636 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 366457266629) ^ 92 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_367595425553 : Nat.Prime 367595425553 := by
  apply lucas_primality 367595425553 (3 : ZMod 367595425553)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (739, 1), (31088923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (739, 1), (31088923, 1)] : List FactorBlock).map factorBlockValue).prod) = 367595425553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_739
      · exact prime_eightySevenCG_31088923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 367595425553) ^ 183797712776 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 367595425553) ^ 497422768 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 367595425553) ^ 11824 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_377183184613 : Nat.Prime 377183184613 := by
  apply lucas_primality 377183184613 (5 : ZMod 377183184613)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (2417840927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (2417840927, 1)] : List FactorBlock).map factorBlockValue).prod) = 377183184613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_2417840927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 377183184613) ^ 188591592306 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 377183184613) ^ 125727728204 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 377183184613) ^ 29014091124 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 377183184613) ^ 156 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_389571740183 : Nat.Prime 389571740183 := by
  apply lucas_primality 389571740183 (5 : ZMod 389571740183)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (571, 1), (341131121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (571, 1), (341131121, 1)] : List FactorBlock).map factorBlockValue).prod) = 389571740183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_571
      · exact prime_eightySevenCG_341131121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 389571740183) ^ 194785870091 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 389571740183) ^ 682262242 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 389571740183) ^ 1142 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_421408014977 : Nat.Prime 421408014977 := by
  apply lucas_primality 421408014977 (3 : ZMod 421408014977)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (13, 1), (433, 1), (584873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (13, 1), (433, 1), (584873, 1)] : List FactorBlock).map factorBlockValue).prod) = 421408014977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_433
      · exact prime_eightySevenCG_584873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 421408014977) ^ 210704007488 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 421408014977) ^ 32416001152 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 421408014977) ^ 973228672 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 421408014977) ^ 720512 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_445509793583 : Nat.Prime 445509793583 := by
  apply lucas_primality 445509793583 (5 : ZMod 445509793583)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (43, 1), (43532323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (43, 1), (43532323, 1)] : List FactorBlock).map factorBlockValue).prod) = 445509793583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_17
      · exact prime_eightySevenCG_43
      · exact prime_eightySevenCG_43532323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 445509793583) ^ 222754896791 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 445509793583) ^ 63644256226 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 445509793583) ^ 26206458446 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 445509793583) ^ 10360692874 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 445509793583) ^ 10234 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_500905718897 : Nat.Prime 500905718897 := by
  apply lucas_primality 500905718897 (3 : ZMod 500905718897)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (17, 1), (41, 1), (1163, 1), (3511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (17, 1), (41, 1), (1163, 1), (3511, 1)] : List FactorBlock).map factorBlockValue).prod) = 500905718897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_17
      · exact prime_eightySevenCG_41
      · exact prime_eightySevenCG_1163
      · exact prime_eightySevenCG_3511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 500905718897) ^ 250452859448 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 500905718897) ^ 45536883536 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 500905718897) ^ 29465042288 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 500905718897) ^ 12217212656 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 500905718897) ^ 430701392 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 500905718897) ^ 142667536 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_506864076899 : Nat.Prime 506864076899 := by
  apply lucas_primality 506864076899 (2 : ZMod 506864076899)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (26717, 1), (9485797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (26717, 1), (9485797, 1)] : List FactorBlock).map factorBlockValue).prod) = 506864076899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_26717
      · exact prime_eightySevenCG_9485797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 506864076899) ^ 253432038449 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 506864076899) ^ 18971594 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 506864076899) ^ 53434 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_525400326263 : Nat.Prime 525400326263 := by
  apply lucas_primality 525400326263 (5 : ZMod 525400326263)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (47, 1), (3191, 1), (35747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (47, 1), (3191, 1), (35747, 1)] : List FactorBlock).map factorBlockValue).prod) = 525400326263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_47
      · exact prime_eightySevenCG_3191
      · exact prime_eightySevenCG_35747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 525400326263) ^ 262700163131 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 525400326263) ^ 75057189466 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 525400326263) ^ 11178730346 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 525400326263) ^ 164650682 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 525400326263) ^ 14697746 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_565580573707 : Nat.Prime 565580573707 := by
  apply lucas_primality 565580573707 (2 : ZMod 565580573707)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (347, 1), (271652533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (347, 1), (271652533, 1)] : List FactorBlock).map factorBlockValue).prod) = 565580573707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_347
      · exact prime_eightySevenCG_271652533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 565580573707) ^ 282790286853 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 565580573707) ^ 188526857902 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 565580573707) ^ 1629915198 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 565580573707) ^ 2082 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_652630450781 : Nat.Prime 652630450781 := by
  apply lucas_primality 652630450781 (2 : ZMod 652630450781)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (11, 1), (71, 1), (5968817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (11, 1), (71, 1), (5968817, 1)] : List FactorBlock).map factorBlockValue).prod) = 652630450781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_71
      · exact prime_eightySevenCG_5968817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 652630450781) ^ 326315225390 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 652630450781) ^ 130526090156 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 652630450781) ^ 93232921540 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 652630450781) ^ 59330040980 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 652630450781) ^ 9191978180 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 652630450781) ^ 109340 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_677120698981 : Nat.Prime 677120698981 := by
  apply lucas_primality 677120698981 (2 : ZMod 677120698981)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (11, 1), (29, 1), (11792419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (11, 1), (29, 1), (11792419, 1)] : List FactorBlock).map factorBlockValue).prod) = 677120698981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_29
      · exact prime_eightySevenCG_11792419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 677120698981) ^ 338560349490 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 677120698981) ^ 225706899660 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 677120698981) ^ 135424139796 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 677120698981) ^ 61556427180 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 677120698981) ^ 23348989620 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 677120698981) ^ 57420 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_836571551089 : Nat.Prime 836571551089 := by
  apply lucas_primality 836571551089 (11 : ZMod 836571551089)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (13, 1), (47, 1), (59, 1), (69067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (13, 1), (47, 1), (59, 1), (69067, 1)] : List FactorBlock).map factorBlockValue).prod) = 836571551089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_47
      · exact prime_eightySevenCG_59
      · exact prime_eightySevenCG_69067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 836571551089) ^ 418285775544 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (11 : ZMod 836571551089) ^ 278857183696 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (11 : ZMod 836571551089) ^ 119510221584 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (11 : ZMod 836571551089) ^ 64351657776 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (11 : ZMod 836571551089) ^ 17799394704 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (11 : ZMod 836571551089) ^ 14179178832 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (11 : ZMod 836571551089) ^ 12112464 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_845208382379 : Nat.Prime 845208382379 := by
  apply lucas_primality 845208382379 (2 : ZMod 845208382379)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (173, 1), (66021589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (173, 1), (66021589, 1)] : List FactorBlock).map factorBlockValue).prod) = 845208382379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_37
      · exact prime_eightySevenCG_173
      · exact prime_eightySevenCG_66021589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 845208382379) ^ 422604191189 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 845208382379) ^ 22843469794 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 845208382379) ^ 4885597586 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 845208382379) ^ 12802 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1010559056789 : Nat.Prime 1010559056789 := by
  apply lucas_primality 1010559056789 (2 : ZMod 1010559056789)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (51481, 1), (4907437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (51481, 1), (4907437, 1)] : List FactorBlock).map factorBlockValue).prod) = 1010559056789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_51481
      · exact prime_eightySevenCG_4907437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1010559056789) ^ 505279528394 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1010559056789) ^ 19629748 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1010559056789) ^ 205924 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1085552086123 : Nat.Prime 1085552086123 := by
  apply lucas_primality 1085552086123 (2 : ZMod 1085552086123)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17, 1), (557, 1), (909863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17, 1), (557, 1), (909863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1085552086123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_17
      · exact prime_eightySevenCG_557
      · exact prime_eightySevenCG_909863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1085552086123) ^ 542776043061 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1085552086123) ^ 361850695374 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1085552086123) ^ 155078869446 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1085552086123) ^ 63856005066 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1085552086123) ^ 1948926546 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1085552086123) ^ 1193094 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1226758895489 : Nat.Prime 1226758895489 := by
  apply lucas_primality 1226758895489 (6 : ZMod 1226758895489)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (37, 1), (37004069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (37, 1), (37004069, 1)] : List FactorBlock).map factorBlockValue).prod) = 1226758895489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_37
      · exact prime_eightySevenCG_37004069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1226758895489) ^ 613379447744 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1226758895489) ^ 175251270784 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1226758895489) ^ 33155645824 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1226758895489) ^ 33152 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1309465093931 : Nat.Prime 1309465093931 := by
  apply lucas_primality 1309465093931 (2 : ZMod 1309465093931)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (19, 2), (101, 1), (513059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (19, 2), (101, 1), (513059, 1)] : List FactorBlock).map factorBlockValue).prod) = 1309465093931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_19
      · exact prime_eightySevenCG_101
      · exact prime_eightySevenCG_513059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1309465093931) ^ 654732546965 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1309465093931) ^ 261893018786 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1309465093931) ^ 187066441990 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1309465093931) ^ 68919215470 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1309465093931) ^ 12965000930 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1309465093931) ^ 2552270 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1439783588501 : Nat.Prime 1439783588501 := by
  apply lucas_primality 1439783588501 (2 : ZMod 1439783588501)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (547, 1), (5264291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (547, 1), (5264291, 1)] : List FactorBlock).map factorBlockValue).prod) = 1439783588501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_547
      · exact prime_eightySevenCG_5264291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1439783588501) ^ 719891794250 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1439783588501) ^ 287956717700 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1439783588501) ^ 2632145500 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1439783588501) ^ 273500 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1465631125853 : Nat.Prime 1465631125853 := by
  apply lucas_primality 1465631125853 (2 : ZMod 1465631125853)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (70321, 1), (274237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (70321, 1), (274237, 1)] : List FactorBlock).map factorBlockValue).prod) = 1465631125853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_19
      · exact prime_eightySevenCG_70321
      · exact prime_eightySevenCG_274237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1465631125853) ^ 732815562926 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1465631125853) ^ 77138480308 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1465631125853) ^ 20842012 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1465631125853) ^ 5344396 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_2549700415441 : Nat.Prime 2549700415441 := by
  apply lucas_primality 2549700415441 (29 : ZMod 2549700415441)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 1), (1180416859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 1), (1180416859, 1)] : List FactorBlock).map factorBlockValue).prod) = 2549700415441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_1180416859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 2549700415441) ^ 1274850207720 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (29 : ZMod 2549700415441) ^ 849900138480 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (29 : ZMod 2549700415441) ^ 509940083088 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (29 : ZMod 2549700415441) ^ 2160 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_2636075560759 : Nat.Prime 2636075560759 := by
  apply lucas_primality 2636075560759 (6 : ZMod 2636075560759)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (701, 1), (5857399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (701, 1), (5857399, 1)] : List FactorBlock).map factorBlockValue).prod) = 2636075560759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_107
      · exact prime_eightySevenCG_701
      · exact prime_eightySevenCG_5857399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2636075560759) ^ 1318037780379 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 2636075560759) ^ 878691853586 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 2636075560759) ^ 24636220194 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 2636075560759) ^ 3760450158 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 2636075560759) ^ 450042 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_3273411979151 : Nat.Prime 3273411979151 := by
  apply lucas_primality 3273411979151 (17 : ZMod 3273411979151)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (65468239583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (65468239583, 1)] : List FactorBlock).map factorBlockValue).prod) = 3273411979151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_65468239583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 3273411979151) ^ 1636705989575 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (17 : ZMod 3273411979151) ^ 654682395830 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (17 : ZMod 3273411979151) ^ 50 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_3446181353399 : Nat.Prime 3446181353399 := by
  apply lucas_primality 3446181353399 (7 : ZMod 3446181353399)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (35165115851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (35165115851, 1)] : List FactorBlock).map factorBlockValue).prod) = 3446181353399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_35165115851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3446181353399) ^ 1723090676699 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 3446181353399) ^ 492311621914 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 3446181353399) ^ 98 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_3461449707031 : Nat.Prime 3461449707031 := by
  apply lucas_primality 3461449707031 (12 : ZMod 3461449707031)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (1823, 1), (9041741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1823, 1), (9041741, 1)] : List FactorBlock).map factorBlockValue).prod) = 3461449707031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_1823
      · exact prime_eightySevenCG_9041741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 3461449707031) ^ 1730724853515 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (12 : ZMod 3461449707031) ^ 1153816569010 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (12 : ZMod 3461449707031) ^ 692289941406 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (12 : ZMod 3461449707031) ^ 494492815290 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (12 : ZMod 3461449707031) ^ 1898765610 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (12 : ZMod 3461449707031) ^ 382830 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_3609040667737 : Nat.Prime 3609040667737 := by
  apply lucas_primality 3609040667737 (10 : ZMod 3609040667737)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (21482384927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (21482384927, 1)] : List FactorBlock).map factorBlockValue).prod) = 3609040667737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_21482384927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 3609040667737) ^ 1804520333868 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 3609040667737) ^ 1203013555912 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 3609040667737) ^ 515577238248 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 3609040667737) ^ 168 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_4350830856079 : Nat.Prime 4350830856079 := by
  apply lucas_primality 4350830856079 (7 : ZMod 4350830856079)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (41, 1), (73, 1), (151, 1), (229213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (41, 1), (73, 1), (151, 1), (229213, 1)] : List FactorBlock).map factorBlockValue).prod) = 4350830856079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_41
      · exact prime_eightySevenCG_73
      · exact prime_eightySevenCG_151
      · exact prime_eightySevenCG_229213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4350830856079) ^ 2175415428039 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4350830856079) ^ 1450276952026 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4350830856079) ^ 621547265154 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4350830856079) ^ 106117825758 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4350830856079) ^ 59600422686 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4350830856079) ^ 28813449378 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4350830856079) ^ 18981606 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_4476888798341 : Nat.Prime 4476888798341 := by
  apply lucas_primality 4476888798341 (3 : ZMod 4476888798341)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (79, 1), (404781989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (79, 1), (404781989, 1)] : List FactorBlock).map factorBlockValue).prod) = 4476888798341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_79
      · exact prime_eightySevenCG_404781989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4476888798341) ^ 2238444399170 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4476888798341) ^ 895377759668 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4476888798341) ^ 639555542620 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4476888798341) ^ 56669478460 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4476888798341) ^ 11060 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_4804809701977 : Nat.Prime 4804809701977 := by
  apply lucas_primality 4804809701977 (7 : ZMod 4804809701977)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (41, 1), (269, 1), (224101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (41, 1), (269, 1), (224101, 1)] : List FactorBlock).map factorBlockValue).prod) = 4804809701977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_41
      · exact prime_eightySevenCG_269
      · exact prime_eightySevenCG_224101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4804809701977) ^ 2402404850988 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4804809701977) ^ 1601603233992 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4804809701977) ^ 117190480536 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4804809701977) ^ 17861746104 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4804809701977) ^ 21440376 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_5027121607457 : Nat.Prime 5027121607457 := by
  apply lucas_primality 5027121607457 (3 : ZMod 5027121607457)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (23, 1), (191, 1), (1621, 1), (1697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (23, 1), (191, 1), (1621, 1), (1697, 1)] : List FactorBlock).map factorBlockValue).prod) = 5027121607457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_23
      · exact prime_eightySevenCG_191
      · exact prime_eightySevenCG_1621
      · exact prime_eightySevenCG_1697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5027121607457) ^ 2513560803728 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5027121607457) ^ 386701662112 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5027121607457) ^ 218570504672 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5027121607457) ^ 26320008416 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5027121607457) ^ 3101247136 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5027121607457) ^ 2962358048 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_5646135876919 : Nat.Prime 5646135876919 := by
  apply lucas_primality 5646135876919 (3 : ZMod 5646135876919)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (173, 1), (587, 1), (9266503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (173, 1), (587, 1), (9266503, 1)] : List FactorBlock).map factorBlockValue).prod) = 5646135876919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_173
      · exact prime_eightySevenCG_587
      · exact prime_eightySevenCG_9266503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5646135876919) ^ 2823067938459 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5646135876919) ^ 1882045292306 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5646135876919) ^ 32636623566 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5646135876919) ^ 9618630114 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5646135876919) ^ 609306 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_6905025521503 : Nat.Prime 6905025521503 := by
  apply lucas_primality 6905025521503 (7 : ZMod 6905025521503)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (28069209437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (28069209437, 1)] : List FactorBlock).map factorBlockValue).prod) = 6905025521503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_41
      · exact prime_eightySevenCG_28069209437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6905025521503) ^ 3452512760751 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 6905025521503) ^ 2301675173834 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 6905025521503) ^ 168415256622 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 6905025521503) ^ 246 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_7243499611333 : Nat.Prime 7243499611333 := by
  apply lucas_primality 7243499611333 (5 : ZMod 7243499611333)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (443, 1), (454194859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (443, 1), (454194859, 1)] : List FactorBlock).map factorBlockValue).prod) = 7243499611333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_443
      · exact prime_eightySevenCG_454194859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7243499611333) ^ 3621749805666 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 7243499611333) ^ 2414499870444 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 7243499611333) ^ 16351014924 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 7243499611333) ^ 15948 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_8221678445143 : Nat.Prime 8221678445143 := by
  apply lucas_primality 8221678445143 (5 : ZMod 8221678445143)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (179, 1), (4219, 1), (604819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (179, 1), (4219, 1), (604819, 1)] : List FactorBlock).map factorBlockValue).prod) = 8221678445143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_179
      · exact prime_eightySevenCG_4219
      · exact prime_eightySevenCG_604819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8221678445143) ^ 4110839222571 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8221678445143) ^ 2740559481714 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8221678445143) ^ 45931164498 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8221678445143) ^ 1948726818 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8221678445143) ^ 13593618 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_8390181807673 : Nat.Prime 8390181807673 := by
  apply lucas_primality 8390181807673 (5 : ZMod 8390181807673)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (311, 1), (160583789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (311, 1), (160583789, 1)] : List FactorBlock).map factorBlockValue).prod) = 8390181807673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_311
      · exact prime_eightySevenCG_160583789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8390181807673) ^ 4195090903836 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8390181807673) ^ 2796727269224 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8390181807673) ^ 1198597401096 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8390181807673) ^ 26978076552 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8390181807673) ^ 52248 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_9906043176871 : Nat.Prime 9906043176871 := by
  apply lucas_primality 9906043176871 (6 : ZMod 9906043176871)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (5171, 1), (63856399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (5171, 1), (63856399, 1)] : List FactorBlock).map factorBlockValue).prod) = 9906043176871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_5171
      · exact prime_eightySevenCG_63856399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9906043176871) ^ 4953021588435 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 9906043176871) ^ 3302014392290 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 9906043176871) ^ 1981208635374 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 9906043176871) ^ 1915691970 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 9906043176871) ^ 155130 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_11011051754531 : Nat.Prime 11011051754531 := by
  apply lucas_primality 11011051754531 (2 : ZMod 11011051754531)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13099, 1), (84060247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13099, 1), (84060247, 1)] : List FactorBlock).map factorBlockValue).prod) = 11011051754531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_13099
      · exact prime_eightySevenCG_84060247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11011051754531) ^ 5505525877265 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11011051754531) ^ 2202210350906 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11011051754531) ^ 840602470 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11011051754531) ^ 130990 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_11246758076467 : Nat.Prime 11246758076467 := by
  apply lucas_primality 11246758076467 (2 : ZMod 11246758076467)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (17, 1), (151, 1), (22127701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (17, 1), (151, 1), (22127701, 1)] : List FactorBlock).map factorBlockValue).prod) = 11246758076467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_17
      · exact prime_eightySevenCG_151
      · exact prime_eightySevenCG_22127701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11246758076467) ^ 5623379038233 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11246758076467) ^ 3748919358822 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11246758076467) ^ 1022432552406 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11246758076467) ^ 661574004498 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11246758076467) ^ 74481841566 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11246758076467) ^ 508266 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_17580691157371 : Nat.Prime 17580691157371 := by
  apply lucas_primality 17580691157371 (2 : ZMod 17580691157371)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (53274821689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (53274821689, 1)] : List FactorBlock).map factorBlockValue).prod) = 17580691157371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_53274821689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17580691157371) ^ 8790345578685 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17580691157371) ^ 5860230385790 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17580691157371) ^ 3516138231474 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17580691157371) ^ 1598244650670 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17580691157371) ^ 330 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_20289770061049 : Nat.Prime 20289770061049 := by
  apply lucas_primality 20289770061049 (7 : ZMod 20289770061049)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (17, 1), (19, 1), (32313079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (17, 1), (19, 1), (32313079, 1)] : List FactorBlock).map factorBlockValue).prod) = 20289770061049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_17
      · exact prime_eightySevenCG_19
      · exact prime_eightySevenCG_32313079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20289770061049) ^ 10144885030524 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 20289770061049) ^ 6763256687016 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 20289770061049) ^ 1193515885944 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 20289770061049) ^ 1067882634792 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 20289770061049) ^ 627912 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_20882709341077 : Nat.Prime 20882709341077 := by
  apply lucas_primality 20882709341077 (5 : ZMod 20882709341077)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (31, 1), (5103301403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (31, 1), (5103301403, 1)] : List FactorBlock).map factorBlockValue).prod) = 20882709341077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_31
      · exact prime_eightySevenCG_5103301403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 20882709341077) ^ 10441354670538 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 20882709341077) ^ 6960903113692 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 20882709341077) ^ 1898428121916 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 20882709341077) ^ 673635785196 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 20882709341077) ^ 4092 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_21363338100451 : Nat.Prime 21363338100451 := by
  apply lucas_primality 21363338100451 (3 : ZMod 21363338100451)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (29, 1), (331, 1), (14837197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (29, 1), (331, 1), (14837197, 1)] : List FactorBlock).map factorBlockValue).prod) = 21363338100451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_29
      · exact prime_eightySevenCG_331
      · exact prime_eightySevenCG_14837197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21363338100451) ^ 10681669050225 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 21363338100451) ^ 7121112700150 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 21363338100451) ^ 4272667620090 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 21363338100451) ^ 736666831050 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 21363338100451) ^ 64541806950 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 21363338100451) ^ 1439850 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_21687348619777 : Nat.Prime 21687348619777 := by
  apply lucas_primality 21687348619777 (10 : ZMod 21687348619777)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (7, 3), (5189, 1), (7933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (7, 3), (5189, 1), (7933, 1)] : List FactorBlock).map factorBlockValue).prod) = 21687348619777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_5189
      · exact prime_eightySevenCG_7933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 21687348619777) ^ 10843674309888 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 21687348619777) ^ 7229116206592 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 21687348619777) ^ 3098192659968 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 21687348619777) ^ 4179485184 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 21687348619777) ^ 2733814272 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_26986221891131 : Nat.Prime 26986221891131 := by
  apply lucas_primality 26986221891131 (2 : ZMod 26986221891131)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (65820053393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (65820053393, 1)] : List FactorBlock).map factorBlockValue).prod) = 26986221891131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_41
      · exact prime_eightySevenCG_65820053393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26986221891131) ^ 13493110945565 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 26986221891131) ^ 5397244378226 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 26986221891131) ^ 658200533930 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 26986221891131) ^ 410 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_33549536094353 : Nat.Prime 33549536094353 := by
  apply lucas_primality 33549536094353 (3 : ZMod 33549536094353)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (73, 1), (643, 1), (44671723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (73, 1), (643, 1), (44671723, 1)] : List FactorBlock).map factorBlockValue).prod) = 33549536094353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_73
      · exact prime_eightySevenCG_643
      · exact prime_eightySevenCG_44671723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 33549536094353) ^ 16774768047176 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 33549536094353) ^ 459582686224 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 33549536094353) ^ 52176572464 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 33549536094353) ^ 751024 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_37736804706277 : Nat.Prime 37736804706277 := by
  apply lucas_primality 37736804706277 (2 : ZMod 37736804706277)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 2), (743, 1), (25044269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 2), (743, 1), (25044269, 1)] : List FactorBlock).map factorBlockValue).prod) = 37736804706277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_743
      · exact prime_eightySevenCG_25044269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37736804706277) ^ 18868402353138 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 37736804706277) ^ 12578934902092 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 37736804706277) ^ 2902831131252 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 37736804706277) ^ 50789777532 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 37736804706277) ^ 1506804 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_52885225328473 : Nat.Prime 52885225328473 := by
  apply lucas_primality 52885225328473 (5 : ZMod 52885225328473)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (163, 1), (4506239377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (163, 1), (4506239377, 1)] : List FactorBlock).map factorBlockValue).prod) = 52885225328473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_163
      · exact prime_eightySevenCG_4506239377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 52885225328473) ^ 26442612664236 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 52885225328473) ^ 17628408442824 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 52885225328473) ^ 324449235144 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 52885225328473) ^ 11736 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_57752110401539 : Nat.Prime 57752110401539 := by
  apply lucas_primality 57752110401539 (2 : ZMod 57752110401539)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (179354380129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (179354380129, 1)] : List FactorBlock).map factorBlockValue).prod) = 57752110401539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_23
      · exact prime_eightySevenCG_179354380129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57752110401539) ^ 28876055200769 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 57752110401539) ^ 8250301485934 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 57752110401539) ^ 2510961321806 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 57752110401539) ^ 322 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_67480548458803 : Nat.Prime 67480548458803 := by
  apply lucas_primality 67480548458803 (3 : ZMod 67480548458803)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11246758076467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11246758076467, 1)] : List FactorBlock).map factorBlockValue).prod) = 67480548458803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_11246758076467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 67480548458803) ^ 33740274229401 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 67480548458803) ^ 22493516152934 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 67480548458803) ^ 6 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_70131991139669 : Nat.Prime 70131991139669 := by
  apply lucas_primality 70131991139669 (2 : ZMod 70131991139669)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (565580573707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (565580573707, 1)] : List FactorBlock).map factorBlockValue).prod) = 70131991139669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_31
      · exact prime_eightySevenCG_565580573707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 70131991139669) ^ 35065995569834 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 70131991139669) ^ 2262322294828 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 70131991139669) ^ 124 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_73132234958963 : Nat.Prime 73132234958963 := by
  apply lucas_primality 73132234958963 (2 : ZMod 73132234958963)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (500905718897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (500905718897, 1)] : List FactorBlock).map factorBlockValue).prod) = 73132234958963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_73
      · exact prime_eightySevenCG_500905718897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 73132234958963) ^ 36566117479481 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 73132234958963) ^ 1001811437794 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 73132234958963) ^ 146 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_77019104463029 : Nat.Prime 77019104463029 := by
  apply lucas_primality 77019104463029 (14 : ZMod 77019104463029)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (3677, 1), (57544451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (3677, 1), (57544451, 1)] : List FactorBlock).map factorBlockValue).prod) = 77019104463029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_3677
      · exact prime_eightySevenCG_57544451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 77019104463029) ^ 38509552231514 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 77019104463029) ^ 11002729209004 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 77019104463029) ^ 5924546497156 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 77019104463029) ^ 20946180164 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 77019104463029) ^ 1338428 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_79620914995283 : Nat.Prime 79620914995283 := by
  apply lucas_primality 79620914995283 (2 : ZMod 79620914995283)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (652630450781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (652630450781, 1)] : List FactorBlock).map factorBlockValue).prod) = 79620914995283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_61
      · exact prime_eightySevenCG_652630450781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 79620914995283) ^ 39810457497641 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 79620914995283) ^ 1305260901562 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 79620914995283) ^ 122 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_100682181692077 : Nat.Prime 100682181692077 := by
  apply lucas_primality 100682181692077 (2 : ZMod 100682181692077)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8390181807673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8390181807673, 1)] : List FactorBlock).map factorBlockValue).prod) = 100682181692077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_8390181807673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 100682181692077) ^ 50341090846038 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 100682181692077) ^ 33560727230692 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 100682181692077) ^ 12 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_113038451509231 : Nat.Prime 113038451509231 := by
  apply lucas_primality 113038451509231 (6 : ZMod 113038451509231)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 1), (23, 1), (577, 1), (7280089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 1), (23, 1), (577, 1), (7280089, 1)] : List FactorBlock).map factorBlockValue).prod) = 113038451509231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_23
      · exact prime_eightySevenCG_577
      · exact prime_eightySevenCG_7280089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 113038451509231) ^ 56519225754615 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 113038451509231) ^ 37679483836410 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 113038451509231) ^ 22607690301846 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 113038451509231) ^ 8695265500710 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 113038451509231) ^ 4914715283010 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 113038451509231) ^ 195907194990 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 113038451509231) ^ 15527070 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_114157455712403 : Nat.Prime 114157455712403 := by
  apply lucas_primality 114157455712403 (2 : ZMod 114157455712403)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (653, 1), (4600526143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (653, 1), (4600526143, 1)] : List FactorBlock).map factorBlockValue).prod) = 114157455712403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_19
      · exact prime_eightySevenCG_653
      · exact prime_eightySevenCG_4600526143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 114157455712403) ^ 57078727856201 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 114157455712403) ^ 6008287142758 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 114157455712403) ^ 174819993434 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 114157455712403) ^ 24814 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_129389119118317 : Nat.Prime 129389119118317 := by
  apply lucas_primality 129389119118317 (2 : ZMod 129389119118317)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (199, 1), (4397, 1), (4107577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (199, 1), (4397, 1), (4107577, 1)] : List FactorBlock).map factorBlockValue).prod) = 129389119118317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_199
      · exact prime_eightySevenCG_4397
      · exact prime_eightySevenCG_4107577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 129389119118317) ^ 64694559559158 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 129389119118317) ^ 43129706372772 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 129389119118317) ^ 650196578484 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 129389119118317) ^ 29426681628 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 129389119118317) ^ 31500108 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_156811215268151 : Nat.Prime 156811215268151 := by
  apply lucas_primality 156811215268151 (13 : ZMod 156811215268151)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7867, 1), (398655689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7867, 1), (398655689, 1)] : List FactorBlock).map factorBlockValue).prod) = 156811215268151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_7867
      · exact prime_eightySevenCG_398655689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 156811215268151) ^ 78405607634075 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 156811215268151) ^ 31362243053630 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 156811215268151) ^ 19932784450 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 156811215268151) ^ 393350 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_168203144180833 : Nat.Prime 168203144180833 := by
  apply lucas_primality 168203144180833 (10 : ZMod 168203144180833)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (79, 1), (22178684623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (79, 1), (22178684623, 1)] : List FactorBlock).map factorBlockValue).prod) = 168203144180833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_79
      · exact prime_eightySevenCG_22178684623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 168203144180833) ^ 84101572090416 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 168203144180833) ^ 56067714726944 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 168203144180833) ^ 2129153723808 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 168203144180833) ^ 7584 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_197792405134217 : Nat.Prime 197792405134217 := by
  apply lucas_primality 197792405134217 (3 : ZMod 197792405134217)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (227, 1), (2083, 1), (52288297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (227, 1), (2083, 1), (52288297, 1)] : List FactorBlock).map factorBlockValue).prod) = 197792405134217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_227
      · exact prime_eightySevenCG_2083
      · exact prime_eightySevenCG_52288297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 197792405134217) ^ 98896202567108 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 197792405134217) ^ 871332181208 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 197792405134217) ^ 94955547352 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 197792405134217) ^ 3782728 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_214491861107897 : Nat.Prime 214491861107897 := by
  apply lucas_primality 214491861107897 (3 : ZMod 214491861107897)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (163, 1), (99013, 1), (1661273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (163, 1), (99013, 1), (1661273, 1)] : List FactorBlock).map factorBlockValue).prod) = 214491861107897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_163
      · exact prime_eightySevenCG_99013
      · exact prime_eightySevenCG_1661273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 214491861107897) ^ 107245930553948 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 214491861107897) ^ 1315900988392 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 214491861107897) ^ 2166299992 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 214491861107897) ^ 129112952 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_293274674389601 : Nat.Prime 293274674389601 := by
  apply lucas_primality 293274674389601 (13 : ZMod 293274674389601)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 2), (19, 1), (34129, 1), (565337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 2), (19, 1), (34129, 1), (565337, 1)] : List FactorBlock).map factorBlockValue).prod) = 293274674389601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_19
      · exact prime_eightySevenCG_34129
      · exact prime_eightySevenCG_565337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 293274674389601) ^ 146637337194800 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 293274674389601) ^ 58654934877920 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 293274674389601) ^ 15435509178400 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 293274674389601) ^ 8593122400 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 293274674389601) ^ 518760800 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_301131773646281 : Nat.Prime 301131773646281 := by
  apply lucas_primality 301131773646281 (3 : ZMod 301131773646281)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (2037803, 1), (3694319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (2037803, 1), (3694319, 1)] : List FactorBlock).map factorBlockValue).prod) = 301131773646281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_2037803
      · exact prime_eightySevenCG_3694319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 301131773646281) ^ 150565886823140 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 301131773646281) ^ 60226354729256 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 301131773646281) ^ 147772760 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 301131773646281) ^ 81512120 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_402728726768309 : Nat.Prime 402728726768309 := by
  apply lucas_primality 402728726768309 (2 : ZMod 402728726768309)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (100682181692077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (100682181692077, 1)] : List FactorBlock).map factorBlockValue).prod) = 402728726768309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_100682181692077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 402728726768309) ^ 201364363384154 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 402728726768309) ^ 4 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_467195145972799 : Nat.Prime 467195145972799 := by
  apply lucas_primality 467195145972799 (6 : ZMod 467195145972799)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (461, 1), (2459, 1), (4057, 1), (16931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (461, 1), (2459, 1), (4057, 1), (16931, 1)] : List FactorBlock).map factorBlockValue).prod) = 467195145972799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_461
      · exact prime_eightySevenCG_2459
      · exact prime_eightySevenCG_4057
      · exact prime_eightySevenCG_16931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 467195145972799) ^ 233597572986399 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 467195145972799) ^ 155731715324266 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 467195145972799) ^ 1013438494518 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 467195145972799) ^ 189993959322 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 467195145972799) ^ 115157788014 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 467195145972799) ^ 27594066858 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_494515870877131 : Nat.Prime 494515870877131 := by
  apply lucas_primality 494515870877131 (2 : ZMod 494515870877131)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (445509793583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (445509793583, 1)] : List FactorBlock).map factorBlockValue).prod) = 494515870877131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_37
      · exact prime_eightySevenCG_445509793583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 494515870877131) ^ 247257935438565 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 494515870877131) ^ 164838623625710 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 494515870877131) ^ 98903174175426 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 494515870877131) ^ 13365293807490 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 494515870877131) ^ 1110 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_526165405788779 : Nat.Prime 526165405788779 := by
  apply lucas_primality 526165405788779 (2 : ZMod 526165405788779)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (53, 1), (239383, 1), (2962273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (53, 1), (239383, 1), (2962273, 1)] : List FactorBlock).map factorBlockValue).prod) = 526165405788779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_53
      · exact prime_eightySevenCG_239383
      · exact prime_eightySevenCG_2962273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 526165405788779) ^ 263082702894389 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 526165405788779) ^ 75166486541254 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 526165405788779) ^ 9927649165826 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 526165405788779) ^ 2198006566 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 526165405788779) ^ 177622186 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_552594269638883 : Nat.Prime 552594269638883 := by
  apply lucas_primality 552594269638883 (2 : ZMod 552594269638883)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (211, 1), (1309465093931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (211, 1), (1309465093931, 1)] : List FactorBlock).map factorBlockValue).prod) = 552594269638883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_211
      · exact prime_eightySevenCG_1309465093931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 552594269638883) ^ 276297134819441 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 552594269638883) ^ 2618930187862 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 552594269638883) ^ 422 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_805839983701381 : Nat.Prime 805839983701381 := by
  apply lucas_primality 805839983701381 (2 : ZMod 805839983701381)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (4476888798341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (4476888798341, 1)] : List FactorBlock).map factorBlockValue).prod) = 805839983701381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_4476888798341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 805839983701381) ^ 402919991850690 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 805839983701381) ^ 268613327900460 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 805839983701381) ^ 161167996740276 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 805839983701381) ^ 180 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_957874871580551 : Nat.Prime 957874871580551 := by
  apply lucas_primality 957874871580551 (7 : ZMod 957874871580551)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (11, 1), (5009, 1), (7095761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (11, 1), (5009, 1), (7095761, 1)] : List FactorBlock).map factorBlockValue).prod) = 957874871580551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_5009
      · exact prime_eightySevenCG_7095761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 957874871580551) ^ 478937435790275 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 957874871580551) ^ 191574974316110 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 957874871580551) ^ 136839267368650 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 957874871580551) ^ 87079533780050 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 957874871580551) ^ 191230758950 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 957874871580551) ^ 134992550 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1252962560464621 : Nat.Prime 1252962560464621 := by
  apply lucas_primality 1252962560464621 (6 : ZMod 1252962560464621)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (20882709341077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (20882709341077, 1)] : List FactorBlock).map factorBlockValue).prod) = 1252962560464621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_20882709341077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1252962560464621) ^ 626481280232310 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1252962560464621) ^ 417654186821540 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1252962560464621) ^ 250592512092924 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1252962560464621) ^ 60 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1267853150138501 : Nat.Prime 1267853150138501 := by
  apply lucas_primality 1267853150138501 (2 : ZMod 1267853150138501)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (109, 1), (51437, 1), (452269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (109, 1), (51437, 1), (452269, 1)] : List FactorBlock).map factorBlockValue).prod) = 1267853150138501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_109
      · exact prime_eightySevenCG_51437
      · exact prime_eightySevenCG_452269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1267853150138501) ^ 633926575069250 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1267853150138501) ^ 253570630027700 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1267853150138501) ^ 11631680276500 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1267853150138501) ^ 24648660500 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1267853150138501) ^ 2803316500 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_2013309904629557 : Nat.Prime 2013309904629557 := by
  apply lucas_primality 2013309904629557 (2 : ZMod 2013309904629557)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (1811, 1), (34591, 1), (618053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (1811, 1), (34591, 1), (618053, 1)] : List FactorBlock).map factorBlockValue).prod) = 2013309904629557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_1811
      · exact prime_eightySevenCG_34591
      · exact prime_eightySevenCG_618053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2013309904629557) ^ 1006654952314778 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2013309904629557) ^ 154869992663812 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2013309904629557) ^ 1111711708796 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2013309904629557) ^ 58203287116 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2013309904629557) ^ 3257503652 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_2113839612136649 : Nat.Prime 2113839612136649 := by
  apply lucas_primality 2113839612136649 (3 : ZMod 2113839612136649)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (8161, 1), (12583, 1), (233917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (8161, 1), (12583, 1), (233917, 1)] : List FactorBlock).map factorBlockValue).prod) = 2113839612136649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_8161
      · exact prime_eightySevenCG_12583
      · exact prime_eightySevenCG_233917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2113839612136649) ^ 1056919806068324 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2113839612136649) ^ 192167237466968 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2113839612136649) ^ 259017229768 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2113839612136649) ^ 167991704056 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2113839612136649) ^ 9036707944 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_3814738449384427 : Nat.Prime 3814738449384427 := by
  apply lucas_primality 3814738449384427 (2 : ZMod 3814738449384427)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (251, 1), (257273, 1), (9845677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (251, 1), (257273, 1), (9845677, 1)] : List FactorBlock).map factorBlockValue).prod) = 3814738449384427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_251
      · exact prime_eightySevenCG_257273
      · exact prime_eightySevenCG_9845677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3814738449384427) ^ 1907369224692213 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3814738449384427) ^ 1271579483128142 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3814738449384427) ^ 15198161152926 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3814738449384427) ^ 14827589562 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3814738449384427) ^ 387453138 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_4851496556629069 : Nat.Prime 4851496556629069 := by
  apply lucas_primality 4851496556629069 (6 : ZMod 4851496556629069)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (36161, 1), (486100663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (36161, 1), (486100663, 1)] : List FactorBlock).map factorBlockValue).prod) = 4851496556629069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_23
      · exact prime_eightySevenCG_36161
      · exact prime_eightySevenCG_486100663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4851496556629069) ^ 2425748278314534 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 4851496556629069) ^ 1617165518876356 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 4851496556629069) ^ 210934632896916 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 4851496556629069) ^ 134163782988 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 4851496556629069) ^ 9980436 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_5850578796717041 : Nat.Prime 5850578796717041 := by
  apply lucas_primality 5850578796717041 (3 : ZMod 5850578796717041)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (73132234958963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (73132234958963, 1)] : List FactorBlock).map factorBlockValue).prod) = 5850578796717041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_73132234958963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5850578796717041) ^ 2925289398358520 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5850578796717041) ^ 1170115759343408 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5850578796717041) ^ 80 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_6298321603591733 : Nat.Prime 6298321603591733 := by
  apply lucas_primality 6298321603591733 (3 : ZMod 6298321603591733)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (13, 1), (11011051754531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (13, 1), (11011051754531, 1)] : List FactorBlock).map factorBlockValue).prod) = 6298321603591733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_11011051754531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6298321603591733) ^ 3149160801795866 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6298321603591733) ^ 572574691235612 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6298321603591733) ^ 484486277199364 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6298321603591733) ^ 572 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_7153463096246239 : Nat.Prime 7153463096246239 := by
  apply lucas_primality 7153463096246239 (3 : ZMod 7153463096246239)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (70131991139669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (70131991139669, 1)] : List FactorBlock).map factorBlockValue).prod) = 7153463096246239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_17
      · exact prime_eightySevenCG_70131991139669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7153463096246239) ^ 3576731548123119 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7153463096246239) ^ 2384487698748746 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7153463096246239) ^ 420791946838014 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7153463096246239) ^ 102 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_7447997012946367 : Nat.Prime 7447997012946367 := by
  apply lucas_primality 7447997012946367 (3 : ZMod 7447997012946367)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (33549536094353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (33549536094353, 1)] : List FactorBlock).map factorBlockValue).prod) = 7447997012946367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_37
      · exact prime_eightySevenCG_33549536094353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7447997012946367) ^ 3723998506473183 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7447997012946367) ^ 2482665670982122 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7447997012946367) ^ 201297216566118 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7447997012946367) ^ 222 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_7607118900831007 : Nat.Prime 7607118900831007 := by
  apply lucas_primality 7607118900831007 (21 : ZMod 7607118900831007)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1267853150138501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1267853150138501, 1)] : List FactorBlock).map factorBlockValue).prod) = 7607118900831007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_1267853150138501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (21 : ZMod 7607118900831007) ^ 3803559450415503 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (21 : ZMod 7607118900831007) ^ 2535706300277002 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (21 : ZMod 7607118900831007) ^ 6 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_9570033710146453 : Nat.Prime 9570033710146453 := by
  apply lucas_primality 9570033710146453 (2 : ZMod 9570033710146453)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (97, 1), (8221678445143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (97, 1), (8221678445143, 1)] : List FactorBlock).map factorBlockValue).prod) = 9570033710146453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_97
      · exact prime_eightySevenCG_8221678445143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9570033710146453) ^ 4785016855073226 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9570033710146453) ^ 3190011236715484 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9570033710146453) ^ 98660141341716 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9570033710146453) ^ 1164 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_10349540207697967 : Nat.Prime 10349540207697967 := by
  apply lucas_primality 10349540207697967 (3 : ZMod 10349540207697967)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (156811215268151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (156811215268151, 1)] : List FactorBlock).map factorBlockValue).prod) = 10349540207697967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_156811215268151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10349540207697967) ^ 5174770103848983 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 10349540207697967) ^ 3449846735899322 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 10349540207697967) ^ 940867291608906 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 10349540207697967) ^ 66 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_21381095702732663 : Nat.Prime 21381095702732663 := by
  apply lucas_primality 21381095702732663 (5 : ZMod 21381095702732663)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (983, 1), (836571551089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (983, 1), (836571551089, 1)] : List FactorBlock).map factorBlockValue).prod) = 21381095702732663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_983
      · exact prime_eightySevenCG_836571551089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 21381095702732663) ^ 10690547851366331 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 21381095702732663) ^ 1644699669440974 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 21381095702732663) ^ 21750860328314 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 21381095702732663) ^ 25558 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_31186664641121359 : Nat.Prime 31186664641121359 := by
  apply lucas_primality 31186664641121359 (3 : ZMod 31186664641121359)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (223, 1), (1226758895489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (223, 1), (1226758895489, 1)] : List FactorBlock).map factorBlockValue).prod) = 31186664641121359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_19
      · exact prime_eightySevenCG_223
      · exact prime_eightySevenCG_1226758895489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 31186664641121359) ^ 15593332320560679 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31186664641121359) ^ 10395554880373786 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31186664641121359) ^ 1641403402164282 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31186664641121359) ^ 139850514085746 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31186664641121359) ^ 25422 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_45782007117397367 : Nat.Prime 45782007117397367 := by
  apply lucas_primality 45782007117397367 (5 : ZMod 45782007117397367)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (28387663, 1), (806371541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (28387663, 1), (806371541, 1)] : List FactorBlock).map factorBlockValue).prod) = 45782007117397367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_28387663
      · exact prime_eightySevenCG_806371541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 45782007117397367) ^ 22891003558698683 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 45782007117397367) ^ 1612743082 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 45782007117397367) ^ 56775326 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_52960208150271817 : Nat.Prime 52960208150271817 := by
  apply lucas_primality 52960208150271817 (10 : ZMod 52960208150271817)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (23, 1), (29, 1), (367595425553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (23, 1), (29, 1), (367595425553, 1)] : List FactorBlock).map factorBlockValue).prod) = 52960208150271817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_23
      · exact prime_eightySevenCG_29
      · exact prime_eightySevenCG_367595425553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 52960208150271817) ^ 26480104075135908 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 52960208150271817) ^ 17653402716757272 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 52960208150271817) ^ 2302617745663992 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 52960208150271817) ^ 1826214074147304 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 52960208150271817) ^ 144072 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_118123102736264947 : Nat.Prime 118123102736264947 := by
  apply lucas_primality 118123102736264947 (2 : ZMod 118123102736264947)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (499, 1), (1071977, 1), (36804217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (499, 1), (1071977, 1), (36804217, 1)] : List FactorBlock).map factorBlockValue).prod) = 118123102736264947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_499
      · exact prime_eightySevenCG_1071977
      · exact prime_eightySevenCG_36804217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 118123102736264947) ^ 59061551368132473 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 118123102736264947) ^ 39374367578754982 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 118123102736264947) ^ 236719644762054 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 118123102736264947) ^ 110191825698 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 118123102736264947) ^ 3209499138 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_143199576587866231 : Nat.Prime 143199576587866231 := by
  apply lucas_primality 143199576587866231 (6 : ZMod 143199576587866231)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (9196273, 1), (173016439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (9196273, 1), (173016439, 1)] : List FactorBlock).map factorBlockValue).prod) = 143199576587866231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_9196273
      · exact prime_eightySevenCG_173016439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 143199576587866231) ^ 71599788293933115 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 143199576587866231) ^ 47733192195955410 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 143199576587866231) ^ 28639915317573246 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 143199576587866231) ^ 15571479510 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 143199576587866231) ^ 827664570 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_191206196280989567 : Nat.Prime 191206196280989567 := by
  apply lucas_primality 191206196280989567 (5 : ZMod 191206196280989567)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (179827, 1), (3183468787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (179827, 1), (3183468787, 1)] : List FactorBlock).map factorBlockValue).prod) = 191206196280989567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_167
      · exact prime_eightySevenCG_179827
      · exact prime_eightySevenCG_3183468787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 191206196280989567) ^ 95603098140494783 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 191206196280989567) ^ 1144947283119698 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 191206196280989567) ^ 1063278574858 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 191206196280989567) ^ 60062218 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_269444793265348021 : Nat.Prime 269444793265348021 := by
  apply lucas_primality 269444793265348021 (2 : ZMod 269444793265348021)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (73, 1), (137, 1), (397, 1), (7433, 1), (8951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (73, 1), (137, 1), (397, 1), (7433, 1), (8951, 1)] : List FactorBlock).map factorBlockValue).prod) = 269444793265348021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_17
      · exact prime_eightySevenCG_73
      · exact prime_eightySevenCG_137
      · exact prime_eightySevenCG_397
      · exact prime_eightySevenCG_7433
      · exact prime_eightySevenCG_8951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 269444793265348021) ^ 134722396632674010 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 269444793265348021) ^ 89814931088449340 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 269444793265348021) ^ 53888958653069604 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 269444793265348021) ^ 15849693721491060 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 269444793265348021) ^ 3691024565278740 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 269444793265348021) ^ 1966750315805460 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 269444793265348021) ^ 678702250038660 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 269444793265348021) ^ 36249804017940 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 269444793265348021) ^ 30102200119020 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_272928116587870619 : Nat.Prime 272928116587870619 := by
  apply lucas_primality 272928116587870619 (2 : ZMod 272928116587870619)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (83, 1), (2220367, 1), (6222551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (83, 1), (2220367, 1), (6222551, 1)] : List FactorBlock).map factorBlockValue).prod) = 272928116587870619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_17
      · exact prime_eightySevenCG_83
      · exact prime_eightySevenCG_2220367
      · exact prime_eightySevenCG_6222551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 272928116587870619) ^ 136464058293935309 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 272928116587870619) ^ 38989730941124374 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 272928116587870619) ^ 16054595093404154 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 272928116587870619) ^ 3288290561299646 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 272928116587870619) ^ 122920272454 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 272928116587870619) ^ 43861129718 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_289920122153216453 : Nat.Prime 289920122153216453 := by
  apply lucas_primality 289920122153216453 (2 : ZMod 289920122153216453)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (3814738449384427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (3814738449384427, 1)] : List FactorBlock).map factorBlockValue).prod) = 289920122153216453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_19
      · exact prime_eightySevenCG_3814738449384427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 289920122153216453) ^ 144960061076608226 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 289920122153216453) ^ 15258953797537708 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 289920122153216453) ^ 76 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_391436286880891997 : Nat.Prime 391436286880891997 := by
  apply lucas_primality 391436286880891997 (2 : ZMod 391436286880891997)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (115781, 1), (845208382379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (115781, 1), (845208382379, 1)] : List FactorBlock).map factorBlockValue).prod) = 391436286880891997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_115781
      · exact prime_eightySevenCG_845208382379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 391436286880891997) ^ 195718143440445998 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 391436286880891997) ^ 3380833529516 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 391436286880891997) ^ 463124 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_428034623037428837 : Nat.Prime 428034623037428837 := by
  apply lucas_primality 428034623037428837 (2 : ZMod 428034623037428837)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (13, 1), (1181, 1), (2267, 1), (279499769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (13, 1), (1181, 1), (2267, 1), (279499769, 1)] : List FactorBlock).map factorBlockValue).prod) = 428034623037428837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_1181
      · exact prime_eightySevenCG_2267
      · exact prime_eightySevenCG_279499769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 428034623037428837) ^ 214017311518714418 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 428034623037428837) ^ 38912238457948076 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 428034623037428837) ^ 32925740233648372 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 428034623037428837) ^ 362434058456756 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 428034623037428837) ^ 188811037952108 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 428034623037428837) ^ 1531431044 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1291796136398220499 : Nat.Prime 1291796136398220499 := by
  apply lucas_primality 1291796136398220499 (2 : ZMod 1291796136398220499)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (10089103, 1), (7113263887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (10089103, 1), (7113263887, 1)] : List FactorBlock).map factorBlockValue).prod) = 1291796136398220499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_10089103
      · exact prime_eightySevenCG_7113263887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1291796136398220499) ^ 645898068199110249 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291796136398220499) ^ 430598712132740166 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291796136398220499) ^ 128038749966 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291796136398220499) ^ 181603854 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1502281020557679991 : Nat.Prime 1502281020557679991 := by
  apply lucas_primality 1502281020557679991 (12 : ZMod 1502281020557679991)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (443, 1), (113038451509231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (443, 1), (113038451509231, 1)] : List FactorBlock).map factorBlockValue).prod) = 1502281020557679991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_443
      · exact prime_eightySevenCG_113038451509231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 1502281020557679991) ^ 751140510278839995 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (12 : ZMod 1502281020557679991) ^ 500760340185893330 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (12 : ZMod 1502281020557679991) ^ 300456204111535998 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (12 : ZMod 1502281020557679991) ^ 3391153545276930 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (12 : ZMod 1502281020557679991) ^ 13290 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1797712347230697251 : Nat.Prime 1797712347230697251 := by
  apply lucas_primality 1797712347230697251 (2 : ZMod 1797712347230697251)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (37, 1), (151, 1), (233, 1), (24527, 1), (225217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (37, 1), (151, 1), (233, 1), (24527, 1), (225217, 1)] : List FactorBlock).map factorBlockValue).prod) = 1797712347230697251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_37
      · exact prime_eightySevenCG_151
      · exact prime_eightySevenCG_233
      · exact prime_eightySevenCG_24527
      · exact prime_eightySevenCG_225217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1797712347230697251) ^ 898856173615348625 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1797712347230697251) ^ 359542469446139450 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1797712347230697251) ^ 48586820195424250 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1797712347230697251) ^ 11905379782984750 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1797712347230697251) ^ 7715503636183250 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1797712347230697251) ^ 73295239826750 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1797712347230697251) ^ 7982134329250 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1828714159693974977 : Nat.Prime 1828714159693974977 := by
  apply lucas_primality 1828714159693974977 (3 : ZMod 1828714159693974977)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (8382713, 1), (3408640943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (8382713, 1), (3408640943, 1)] : List FactorBlock).map factorBlockValue).prod) = 1828714159693974977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_8382713
      · exact prime_eightySevenCG_3408640943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1828714159693974977) ^ 914357079846987488 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1828714159693974977) ^ 218153020352 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1828714159693974977) ^ 536493632 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1977124997128183337 : Nat.Prime 1977124997128183337 := by
  apply lucas_primality 1977124997128183337 (3 : ZMod 1977124997128183337)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (19, 1), (137, 1), (1201, 1), (1613358511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (19, 1), (137, 1), (1201, 1), (1613358511, 1)] : List FactorBlock).map factorBlockValue).prod) = 1977124997128183337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_19
      · exact prime_eightySevenCG_137
      · exact prime_eightySevenCG_1201
      · exact prime_eightySevenCG_1613358511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1977124997128183337) ^ 988562498564091668 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1977124997128183337) ^ 282446428161169048 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1977124997128183337) ^ 104059210375167544 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1977124997128183337) ^ 14431569322103528 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1977124997128183337) ^ 1646232304020136 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1977124997128183337) ^ 1225471576 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_2384434158119359499 : Nat.Prime 2384434158119359499 := by
  apply lucas_primality 2384434158119359499 (2 : ZMod 2384434158119359499)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (237157, 1), (5027121607457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (237157, 1), (5027121607457, 1)] : List FactorBlock).map factorBlockValue).prod) = 2384434158119359499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_237157
      · exact prime_eightySevenCG_5027121607457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2384434158119359499) ^ 1192217079059679749 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2384434158119359499) ^ 10054243214914 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2384434158119359499) ^ 474314 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_3771863969699771381 : Nat.Prime 3771863969699771381 := by
  apply lucas_primality 3771863969699771381 (2 : ZMod 3771863969699771381)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (346726979, 1), (543924211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (346726979, 1), (543924211, 1)] : List FactorBlock).map factorBlockValue).prod) = 3771863969699771381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_346726979
      · exact prime_eightySevenCG_543924211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3771863969699771381) ^ 1885931984849885690 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3771863969699771381) ^ 754372793939954276 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3771863969699771381) ^ 10878484220 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3771863969699771381) ^ 6934539580 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_4988149499111548391 : Nat.Prime 4988149499111548391 := by
  apply lucas_primality 4988149499111548391 (13 : ZMod 4988149499111548391)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (619, 1), (805839983701381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (619, 1), (805839983701381, 1)] : List FactorBlock).map factorBlockValue).prod) = 4988149499111548391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_619
      · exact prime_eightySevenCG_805839983701381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 4988149499111548391) ^ 2494074749555774195 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 4988149499111548391) ^ 997629899822309678 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 4988149499111548391) ^ 8058399837013810 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (13 : ZMod 4988149499111548391) ^ 6190 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_6856364360536881763 : Nat.Prime 6856364360536881763 := by
  apply lucas_primality 6856364360536881763 (2 : ZMod 6856364360536881763)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (70583, 1), (177953, 1), (636211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (70583, 1), (177953, 1), (636211, 1)] : List FactorBlock).map factorBlockValue).prod) = 6856364360536881763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_70583
      · exact prime_eightySevenCG_177953
      · exact prime_eightySevenCG_636211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6856364360536881763) ^ 3428182180268440881 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6856364360536881763) ^ 2285454786845627254 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6856364360536881763) ^ 623305850957898342 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6856364360536881763) ^ 527412643118221674 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6856364360536881763) ^ 97139032919214 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6856364360536881763) ^ 38529074309154 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6856364360536881763) ^ 10776871761942 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_7061073754468072069 : Nat.Prime 7061073754468072069 := by
  apply lucas_primality 7061073754468072069 (2 : ZMod 7061073754468072069)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (25601, 1), (441011, 1), (17372483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (25601, 1), (441011, 1), (17372483, 1)] : List FactorBlock).map factorBlockValue).prod) = 7061073754468072069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_25601
      · exact prime_eightySevenCG_441011
      · exact prime_eightySevenCG_17372483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7061073754468072069) ^ 3530536877234036034 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7061073754468072069) ^ 2353691251489357356 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7061073754468072069) ^ 275812419611268 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7061073754468072069) ^ 16011105742188 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7061073754468072069) ^ 406451613996 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_8202558595892204917 : Nat.Prime 8202558595892204917 := by
  apply lucas_primality 8202558595892204917 (2 : ZMod 8202558595892204917)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (573343, 1), (44156009363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (573343, 1), (44156009363, 1)] : List FactorBlock).map factorBlockValue).prod) = 8202558595892204917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_573343
      · exact prime_eightySevenCG_44156009363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8202558595892204917) ^ 4101279297946102458 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8202558595892204917) ^ 2734186198630734972 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8202558595892204917) ^ 14306547033612 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8202558595892204917) ^ 185763132 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_8367639656874110341 : Nat.Prime 8367639656874110341 := by
  apply lucas_primality 8367639656874110341 (6 : ZMod 8367639656874110341)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (13, 1), (41, 1), (89, 1), (1567, 1), (268020163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (13, 1), (41, 1), (89, 1), (1567, 1), (268020163, 1)] : List FactorBlock).map factorBlockValue).prod) = 8367639656874110341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_41
      · exact prime_eightySevenCG_89
      · exact prime_eightySevenCG_1567
      · exact prime_eightySevenCG_268020163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8367639656874110341) ^ 4183819828437055170 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 8367639656874110341) ^ 2789213218958036780 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 8367639656874110341) ^ 1673527931374822068 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 8367639656874110341) ^ 1195377093839158620 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 8367639656874110341) ^ 643664588990316180 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 8367639656874110341) ^ 204088772118880740 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 8367639656874110341) ^ 94018423110945060 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 8367639656874110341) ^ 5339910438337020 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 8367639656874110341) ^ 31220187180 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_9675967401649650943 : Nat.Prime 9675967401649650943 := by
  apply lucas_primality 9675967401649650943 (3 : ZMod 9675967401649650943)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (89, 1), (2013309904629557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (89, 1), (2013309904629557, 1)] : List FactorBlock).map factorBlockValue).prod) = 9675967401649650943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_89
      · exact prime_eightySevenCG_2013309904629557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9675967401649650943) ^ 4837983700824825471 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9675967401649650943) ^ 3225322467216550314 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9675967401649650943) ^ 108718734849996078 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9675967401649650943) ^ 4806 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_10529231922715873253 : Nat.Prime 10529231922715873253 := by
  apply lucas_primality 10529231922715873253 (2 : ZMod 10529231922715873253)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5323, 1), (494515870877131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5323, 1), (494515870877131, 1)] : List FactorBlock).map factorBlockValue).prod) = 10529231922715873253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5323
      · exact prime_eightySevenCG_494515870877131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10529231922715873253) ^ 5264615961357936626 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10529231922715873253) ^ 1978063483508524 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10529231922715873253) ^ 21292 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_10827489627492447719 : Nat.Prime 10827489627492447719 := by
  apply lucas_primality 10827489627492447719 (17 : ZMod 10827489627492447719)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13043, 1), (584531, 1), (710088923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13043, 1), (584531, 1), (710088923, 1)] : List FactorBlock).map factorBlockValue).prod) = 10827489627492447719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_13043
      · exact prime_eightySevenCG_584531
      · exact prime_eightySevenCG_710088923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 10827489627492447719) ^ 5413744813746223859 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (17 : ZMod 10827489627492447719) ^ 830137976500226 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (17 : ZMod 10827489627492447719) ^ 18523379645378 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (17 : ZMod 10827489627492447719) ^ 15248075666 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_45831763861670799437 : Nat.Prime 45831763861670799437 := by
  apply lucas_primality 45831763861670799437 (2 : ZMod 45831763861670799437)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (118123102736264947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (118123102736264947, 1)] : List FactorBlock).map factorBlockValue).prod) = 45831763861670799437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_97
      · exact prime_eightySevenCG_118123102736264947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45831763861670799437) ^ 22915881930835399718 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 45831763861670799437) ^ 472492410945059788 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 45831763861670799437) ^ 388 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_79196258875268352971 : Nat.Prime 79196258875268352971 := by
  apply lucas_primality 79196258875268352971 (6 : ZMod 79196258875268352971)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (107, 1), (13109, 1), (5646135876919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (107, 1), (13109, 1), (5646135876919, 1)] : List FactorBlock).map factorBlockValue).prod) = 79196258875268352971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_107
      · exact prime_eightySevenCG_13109
      · exact prime_eightySevenCG_5646135876919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 79196258875268352971) ^ 39598129437634176485 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 79196258875268352971) ^ 15839251775053670594 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 79196258875268352971) ^ 740151952105311710 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 79196258875268352971) ^ 6041365388303330 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 79196258875268352971) ^ 14026630 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_158392517750536705943 : Nat.Prime 158392517750536705943 := by
  apply lucas_primality 158392517750536705943 (5 : ZMod 158392517750536705943)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79196258875268352971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79196258875268352971, 1)] : List FactorBlock).map factorBlockValue).prod) = 158392517750536705943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_79196258875268352971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 158392517750536705943) ^ 79196258875268352971 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 158392517750536705943) ^ 2 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_181771028626034475961 : Nat.Prime 181771028626034475961 := by
  apply lucas_primality 181771028626034475961 (23 : ZMod 181771028626034475961)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (6491, 1), (4547567, 1), (51315989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (6491, 1), (4547567, 1), (51315989, 1)] : List FactorBlock).map factorBlockValue).prod) = 181771028626034475961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_6491
      · exact prime_eightySevenCG_4547567
      · exact prime_eightySevenCG_51315989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 181771028626034475961) ^ 90885514313017237980 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (23 : ZMod 181771028626034475961) ^ 60590342875344825320 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (23 : ZMod 181771028626034475961) ^ 36354205725206895192 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (23 : ZMod 181771028626034475961) ^ 28003547777851560 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (23 : ZMod 181771028626034475961) ^ 39971050151880 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (23 : ZMod 181771028626034475961) ^ 3542190887640 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_225648119610271748699 : Nat.Prime 225648119610271748699 := by
  apply lucas_primality 225648119610271748699 (2 : ZMod 225648119610271748699)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (641866553, 1), (2282791529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (641866553, 1), (2282791529, 1)] : List FactorBlock).map factorBlockValue).prod) = 225648119610271748699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_641866553
      · exact prime_eightySevenCG_2282791529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 225648119610271748699) ^ 112824059805135874349 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 225648119610271748699) ^ 32235445658610249814 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 225648119610271748699) ^ 20513465419115613518 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 225648119610271748699) ^ 351549895466 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 225648119610271748699) ^ 98847449162 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_244256243013676606129 : Nat.Prime 244256243013676606129 := by
  apply lucas_primality 244256243013676606129 (11 : ZMod 244256243013676606129)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (391436286880891997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (391436286880891997, 1)] : List FactorBlock).map factorBlockValue).prod) = 244256243013676606129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_391436286880891997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 244256243013676606129) ^ 122128121506838303064 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (11 : ZMod 244256243013676606129) ^ 81418747671225535376 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (11 : ZMod 244256243013676606129) ^ 18788941770282815856 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (11 : ZMod 244256243013676606129) ^ 624 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_260441739863456847383 : Nat.Prime 260441739863456847383 := by
  apply lucas_primality 260441739863456847383 (5 : ZMod 260441739863456847383)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (51637, 1), (2980993, 1), (5677699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (51637, 1), (2980993, 1), (5677699, 1)] : List FactorBlock).map factorBlockValue).prod) = 260441739863456847383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_149
      · exact prime_eightySevenCG_51637
      · exact prime_eightySevenCG_2980993
      · exact prime_eightySevenCG_5677699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 260441739863456847383) ^ 130220869931728423691 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 260441739863456847383) ^ 1747931140023200318 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 260441739863456847383) ^ 5043703930581886 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 260441739863456847383) ^ 87367444292374 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 260441739863456847383) ^ 45871001591218 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_493200900389513847577 : Nat.Prime 493200900389513847577 := by
  apply lucas_primality 493200900389513847577 (5 : ZMod 493200900389513847577)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (107, 1), (971, 1), (197792405134217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (107, 1), (971, 1), (197792405134217, 1)] : List FactorBlock).map factorBlockValue).prod) = 493200900389513847577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_107
      · exact prime_eightySevenCG_971
      · exact prime_eightySevenCG_197792405134217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 493200900389513847577) ^ 246600450194756923788 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 493200900389513847577) ^ 164400300129837949192 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 493200900389513847577) ^ 4609354209247792968 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 493200900389513847577) ^ 507930896384669256 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 493200900389513847577) ^ 2493528 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_733081275488612651243 : Nat.Prime 733081275488612651243 := by
  apply lucas_primality 733081275488612651243 (2 : ZMod 733081275488612651243)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4959523, 1), (8440373, 1), (8756299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4959523, 1), (8440373, 1), (8756299, 1)] : List FactorBlock).map factorBlockValue).prod) = 733081275488612651243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_4959523
      · exact prime_eightySevenCG_8440373
      · exact prime_eightySevenCG_8756299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 733081275488612651243) ^ 366540637744306325621 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 733081275488612651243) ^ 147812859319054 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 733081275488612651243) ^ 86854132570754 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 733081275488612651243) ^ 83720448044158 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_735883287593214955993 : Nat.Prime 735883287593214955993 := by
  apply lucas_primality 735883287593214955993 (10 : ZMod 735883287593214955993)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (101, 1), (1117, 1), (605147, 1), (64159981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (101, 1), (1117, 1), (605147, 1), (64159981, 1)] : List FactorBlock).map factorBlockValue).prod) = 735883287593214955993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_101
      · exact prime_eightySevenCG_1117
      · exact prime_eightySevenCG_605147
      · exact prime_eightySevenCG_64159981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 735883287593214955993) ^ 367941643796607477996 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 735883287593214955993) ^ 245294429197738318664 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 735883287593214955993) ^ 105126183941887850856 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 735883287593214955993) ^ 7285973144487276792 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 735883287593214955993) ^ 658803301336808376 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 735883287593214955993) ^ 1216040544848136 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (10 : ZMod 735883287593214955993) ^ 11469506008632 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_1024079929428625987121 : Nat.Prime 1024079929428625987121 := by
  apply lucas_primality 1024079929428625987121 (3 : ZMod 1024079929428625987121)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (1828714159693974977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (1828714159693974977, 1)] : List FactorBlock).map factorBlockValue).prod) = 1024079929428625987121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_1828714159693974977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1024079929428625987121) ^ 512039964714312993560 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1024079929428625987121) ^ 204815985885725197424 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1024079929428625987121) ^ 146297132775517998160 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1024079929428625987121) ^ 560 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_3766378299279529695799 : Nat.Prime 3766378299279529695799 := by
  apply lucas_primality 3766378299279529695799 (3 : ZMod 3766378299279529695799)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (647917, 1), (2615903, 1), (3461369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (647917, 1), (2615903, 1), (3461369, 1)] : List FactorBlock).map factorBlockValue).prod) = 3766378299279529695799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_107
      · exact prime_eightySevenCG_647917
      · exact prime_eightySevenCG_2615903
      · exact prime_eightySevenCG_3461369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3766378299279529695799) ^ 1883189149639764847899 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3766378299279529695799) ^ 1255459433093176565266 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3766378299279529695799) ^ 35199797189528314914 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3766378299279529695799) ^ 5813056763874894 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3766378299279529695799) ^ 1439800443395466 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3766378299279529695799) ^ 1088118111440742 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_3807231711882765039721 : Nat.Prime 3807231711882765039721 := by
  apply lucas_primality 3807231711882765039721 (31 : ZMod 3807231711882765039721)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (7, 1), (11, 1), (45782007117397367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (7, 1), (11, 1), (45782007117397367, 1)] : List FactorBlock).map factorBlockValue).prod) = 3807231711882765039721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_45782007117397367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 3807231711882765039721) ^ 1903615855941382519860 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (31 : ZMod 3807231711882765039721) ^ 1269077237294255013240 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (31 : ZMod 3807231711882765039721) ^ 761446342376553007944 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (31 : ZMod 3807231711882765039721) ^ 543890244554680719960 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (31 : ZMod 3807231711882765039721) ^ 346111973807524094520 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (31 : ZMod 3807231711882765039721) ^ 83160 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_4480677130993804905341 : Nat.Prime 4480677130993804905341 := by
  apply lucas_primality 4480677130993804905341 (3 : ZMod 4480677130993804905341)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (449, 1), (183166199, 1), (247644847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (449, 1), (183166199, 1), (247644847, 1)] : List FactorBlock).map factorBlockValue).prod) = 4480677130993804905341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_449
      · exact prime_eightySevenCG_183166199
      · exact prime_eightySevenCG_247644847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4480677130993804905341) ^ 2240338565496902452670 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4480677130993804905341) ^ 896135426198760981068 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4480677130993804905341) ^ 407334284635800445940 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4480677130993804905341) ^ 9979236371923841660 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4480677130993804905341) ^ 24462357986660 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4480677130993804905341) ^ 18093157137220 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_8334135675630619116257 : Nat.Prime 8334135675630619116257 := by
  apply lucas_primality 8334135675630619116257 (3 : ZMod 8334135675630619116257)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (260441739863456847383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (260441739863456847383, 1)] : List FactorBlock).map factorBlockValue).prod) = 8334135675630619116257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_260441739863456847383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 8334135675630619116257) ^ 4167067837815309558128 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8334135675630619116257) ^ 32 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_8724027603561659624759 : Nat.Prime 8724027603561659624759 := by
  apply lucas_primality 8724027603561659624759 (31 : ZMod 8724027603561659624759)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (1248126881, 1), (47874630883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (1248126881, 1), (47874630883, 1)] : List FactorBlock).map factorBlockValue).prod) = 8724027603561659624759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_73
      · exact prime_eightySevenCG_1248126881
      · exact prime_eightySevenCG_47874630883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (31 : ZMod 8724027603561659624759) ^ 4362013801780829812379 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (31 : ZMod 8724027603561659624759) ^ 119507227446050131846 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (31 : ZMod 8724027603561659624759) ^ 6989696108918 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (31 : ZMod 8724027603561659624759) ^ 182226524626 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_8970905598153924011557 : Nat.Prime 8970905598153924011557 := by
  apply lucas_primality 8970905598153924011557 (2 : ZMod 8970905598153924011557)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (71, 1), (10529231922715873253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (71, 1), (10529231922715873253, 1)] : List FactorBlock).map factorBlockValue).prod) = 8970905598153924011557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_71
      · exact prime_eightySevenCG_10529231922715873253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8970905598153924011557) ^ 4485452799076962005778 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8970905598153924011557) ^ 2990301866051308003852 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8970905598153924011557) ^ 126350783072590479036 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8970905598153924011557) ^ 852 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_9118935816146923634471 : Nat.Prime 9118935816146923634471 := by
  apply lucas_primality 9118935816146923634471 (14 : ZMod 9118935816146923634471)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (23741, 1), (526165405788779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (23741, 1), (526165405788779, 1)] : List FactorBlock).map factorBlockValue).prod) = 9118935816146923634471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_73
      · exact prime_eightySevenCG_23741
      · exact prime_eightySevenCG_526165405788779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 9118935816146923634471) ^ 4559467908073461817235 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 9118935816146923634471) ^ 1823787163229384726894 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 9118935816146923634471) ^ 124916928988314022390 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 9118935816146923634471) ^ 384100746225808670 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 9118935816146923634471) ^ 17330930 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_10802986153502080001131 : Nat.Prime 10802986153502080001131 := by
  apply lucas_primality 10802986153502080001131 (2 : ZMod 10802986153502080001131)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (37, 1), (327491, 1), (9906043176871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (37, 1), (327491, 1), (9906043176871, 1)] : List FactorBlock).map factorBlockValue).prod) = 10802986153502080001131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_37
      · exact prime_eightySevenCG_327491
      · exact prime_eightySevenCG_9906043176871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10802986153502080001131) ^ 5401493076751040000565 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10802986153502080001131) ^ 3600995384500693333710 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10802986153502080001131) ^ 2160597230700416000226 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10802986153502080001131) ^ 291972598743299459490 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10802986153502080001131) ^ 32987123778980430 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10802986153502080001131) ^ 1090545030 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_11004858586733549407169 : Nat.Prime 11004858586733549407169 := by
  apply lucas_primality 11004858586733549407169 (3 : ZMod 11004858586733549407169)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (13, 1), (281, 1), (30889267, 1), (1523867537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (13, 1), (281, 1), (30889267, 1), (1523867537, 1)] : List FactorBlock).map factorBlockValue).prod) = 11004858586733549407169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_281
      · exact prime_eightySevenCG_30889267
      · exact prime_eightySevenCG_1523867537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11004858586733549407169) ^ 5502429293366774703584 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11004858586733549407169) ^ 846527583594888415936 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11004858586733549407169) ^ 39163197817557115328 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11004858586733549407169) ^ 356268039210304 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11004858586733549407169) ^ 7221663510464 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_11063541999242929088317 : Nat.Prime 11063541999242929088317 := by
  apply lucas_primality 11063541999242929088317 (2 : ZMod 11063541999242929088317)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (151, 1), (90481, 1), (67480548458803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (151, 1), (90481, 1), (67480548458803, 1)] : List FactorBlock).map factorBlockValue).prod) = 11063541999242929088317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_151
      · exact prime_eightySevenCG_90481
      · exact prime_eightySevenCG_67480548458803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11063541999242929088317) ^ 5531770999621464544158 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11063541999242929088317) ^ 3687847333080976362772 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11063541999242929088317) ^ 73268490061211450916 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11063541999242929088317) ^ 122274753807351036 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11063541999242929088317) ^ 163951572 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_11637513328678528147793 : Nat.Prime 11637513328678528147793 := by
  apply lucas_primality 11637513328678528147793 (3 : ZMod 11637513328678528147793)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (156775799, 1), (356876403551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (156775799, 1), (356876403551, 1)] : List FactorBlock).map factorBlockValue).prod) = 11637513328678528147793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_156775799
      · exact prime_eightySevenCG_356876403551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11637513328678528147793) ^ 5818756664339264073896 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11637513328678528147793) ^ 895193332975271395984 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11637513328678528147793) ^ 74230291938608 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11637513328678528147793) ^ 32609366192 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_18373532059062257889389 : Nat.Prime 18373532059062257889389 := by
  apply lucas_primality 18373532059062257889389 (2 : ZMod 18373532059062257889389)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (158392517750536705943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (158392517750536705943, 1)] : List FactorBlock).map factorBlockValue).prod) = 18373532059062257889389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_29
      · exact prime_eightySevenCG_158392517750536705943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18373532059062257889389) ^ 9186766029531128944694 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 18373532059062257889389) ^ 633570071002146823772 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 18373532059062257889389) ^ 116 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_21605164483254924743999 : Nat.Prime 21605164483254924743999 := by
  apply lucas_primality 21605164483254924743999 (7 : ZMod 21605164483254924743999)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1831, 1), (8713109, 1), (677120698981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1831, 1), (8713109, 1), (677120698981, 1)] : List FactorBlock).map factorBlockValue).prod) = 21605164483254924743999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_1831
      · exact prime_eightySevenCG_8713109
      · exact prime_eightySevenCG_677120698981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 21605164483254924743999) ^ 10802582241627462371999 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 21605164483254924743999) ^ 11799652912755283858 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 21605164483254924743999) ^ 2479615999668422 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 21605164483254924743999) ^ 31907405158 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_22113597417361588608779 : Nat.Prime 22113597417361588608779 := by
  apply lucas_primality 22113597417361588608779 (6 : ZMod 22113597417361588608779)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (66377, 1), (3535163, 1), (611943907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (66377, 1), (3535163, 1), (611943907, 1)] : List FactorBlock).map factorBlockValue).prod) = 22113597417361588608779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_66377
      · exact prime_eightySevenCG_3535163
      · exact prime_eightySevenCG_611943907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 22113597417361588608779) ^ 11056798708680794304389 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 22113597417361588608779) ^ 3159085345337369801254 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 22113597417361588608779) ^ 2010327037941962600798 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 22113597417361588608779) ^ 333151504547683514 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 22113597417361588608779) ^ 6255326110100606 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 22113597417361588608779) ^ 36136641225454 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_61179633588530291799821 : Nat.Prime 61179633588530291799821 := by
  apply lucas_primality 61179633588530291799821 (2 : ZMod 61179633588530291799821)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (811, 1), (3771863969699771381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (811, 1), (3771863969699771381, 1)] : List FactorBlock).map factorBlockValue).prod) = 61179633588530291799821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_811
      · exact prime_eightySevenCG_3771863969699771381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61179633588530291799821) ^ 30589816794265145899910 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 61179633588530291799821) ^ 12235926717706058359964 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 61179633588530291799821) ^ 75437279393995427620 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 61179633588530291799821) ^ 16220 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_66381251995457574529903 : Nat.Prime 66381251995457574529903 := by
  apply lucas_primality 66381251995457574529903 (3 : ZMod 66381251995457574529903)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11063541999242929088317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11063541999242929088317, 1)] : List FactorBlock).map factorBlockValue).prod) = 66381251995457574529903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_11063541999242929088317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 66381251995457574529903) ^ 33190625997728787264951 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 66381251995457574529903) ^ 22127083998485858176634 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 66381251995457574529903) ^ 6 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_66496650780316270445227 : Nat.Prime 66496650780316270445227 := by
  apply lucas_primality 66496650780316270445227 (3 : ZMod 66496650780316270445227)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (67, 1), (11475623, 1), (4804809701977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (67, 1), (11475623, 1), (4804809701977, 1)] : List FactorBlock).map factorBlockValue).prod) = 66496650780316270445227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_67
      · exact prime_eightySevenCG_11475623
      · exact prime_eightySevenCG_4804809701977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 66496650780316270445227) ^ 33248325390158135222613 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 66496650780316270445227) ^ 22165550260105423481742 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 66496650780316270445227) ^ 992487325079347320078 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 66496650780316270445227) ^ 5794600500584262 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 66496650780316270445227) ^ 13839601338 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_302472302765568946415987 : Nat.Prime 302472302765568946415987 := by
  apply lucas_primality 302472302765568946415987 (2 : ZMod 302472302765568946415987)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (21605164483254924743999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (21605164483254924743999, 1)] : List FactorBlock).map factorBlockValue).prod) = 302472302765568946415987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_21605164483254924743999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 302472302765568946415987) ^ 151236151382784473207993 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 302472302765568946415987) ^ 43210328966509849487998 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 302472302765568946415987) ^ 14 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_820704223453223127102391 : Nat.Prime 820704223453223127102391 := by
  apply lucas_primality 820704223453223127102391 (3 : ZMod 820704223453223127102391)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (9118935816146923634471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (9118935816146923634471, 1)] : List FactorBlock).map factorBlockValue).prod) = 820704223453223127102391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_9118935816146923634471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 820704223453223127102391) ^ 410352111726611563551195 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 820704223453223127102391) ^ 273568074484407709034130 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 820704223453223127102391) ^ 164140844690644625420478 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 820704223453223127102391) ^ 90 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_855176584829438525337461 : Nat.Prime 855176584829438525337461 := by
  apply lucas_primality 855176584829438525337461 (2 : ZMod 855176584829438525337461)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (22381, 1), (272928116587870619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (22381, 1), (272928116587870619, 1)] : List FactorBlock).map factorBlockValue).prod) = 855176584829438525337461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_22381
      · exact prime_eightySevenCG_272928116587870619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 855176584829438525337461) ^ 427588292414719262668730 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 855176584829438525337461) ^ 171035316965887705067492 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 855176584829438525337461) ^ 122168083547062646476780 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 855176584829438525337461) ^ 38209936322301886660 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 855176584829438525337461) ^ 3133340 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_902018932885605087025243 : Nat.Prime 902018932885605087025243 := by
  apply lucas_primality 902018932885605087025243 (5 : ZMod 902018932885605087025243)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (61, 1), (167, 1), (7983617, 1), (24006435329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (61, 1), (167, 1), (7983617, 1), (24006435329, 1)] : List FactorBlock).map factorBlockValue).prod) = 902018932885605087025243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_61
      · exact prime_eightySevenCG_167
      · exact prime_eightySevenCG_7983617
      · exact prime_eightySevenCG_24006435329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 902018932885605087025243) ^ 451009466442802543512621 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 902018932885605087025243) ^ 300672977628535029008414 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 902018932885605087025243) ^ 128859847555086441003606 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 902018932885605087025243) ^ 82001721171418644275022 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 902018932885605087025243) ^ 14787195621075493229922 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 902018932885605087025243) ^ 5401310975362904712726 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 902018932885605087025243) ^ 112983743193793626 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 902018932885605087025243) ^ 37574047147098 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_3643413939178404876677711 : Nat.Prime 3643413939178404876677711 := by
  apply lucas_primality 3643413939178404876677711 (14 : ZMod 3643413939178404876677711)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (71, 1), (733081275488612651243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (71, 1), (733081275488612651243, 1)] : List FactorBlock).map factorBlockValue).prod) = 3643413939178404876677711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_71
      · exact prime_eightySevenCG_733081275488612651243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 3643413939178404876677711) ^ 1821706969589202438338855 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 3643413939178404876677711) ^ 728682787835680975335542 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 3643413939178404876677711) ^ 520487705596914982382530 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 3643413939178404876677711) ^ 51315689284202885587010 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 3643413939178404876677711) ^ 4970 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_6672973849548822374042329 : Nat.Prime 6672973849548822374042329 := by
  apply lucas_primality 6672973849548822374042329 (7 : ZMod 6672973849548822374042329)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (5926155637, 1), (3609040667737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (5926155637, 1), (3609040667737, 1)] : List FactorBlock).map factorBlockValue).prod) = 6672973849548822374042329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_5926155637
      · exact prime_eightySevenCG_3609040667737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6672973849548822374042329) ^ 3336486924774411187021164 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 6672973849548822374042329) ^ 2224324616516274124680776 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 6672973849548822374042329) ^ 513305680734524798003256 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 6672973849548822374042329) ^ 1126020688333944 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 6672973849548822374042329) ^ 1848960558744 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_14937150583349629403643401 : Nat.Prime 14937150583349629403643401 := by
  apply lucas_primality 14937150583349629403643401 (3 : ZMod 14937150583349629403643401)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (1889, 1), (5527, 1), (7153463096246239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (1889, 1), (5527, 1), (7153463096246239, 1)] : List FactorBlock).map factorBlockValue).prod) = 14937150583349629403643401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_1889
      · exact prime_eightySevenCG_5527
      · exact prime_eightySevenCG_7153463096246239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14937150583349629403643401) ^ 7468575291674814701821700 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14937150583349629403643401) ^ 2987430116669925880728680 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14937150583349629403643401) ^ 7907438106590592590600 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14937150583349629403643401) ^ 2702578357761829094200 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14937150583349629403643401) ^ 2088100600 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_31216151416371941752196801 : Nat.Prime 31216151416371941752196801 := by
  apply lucas_primality 31216151416371941752196801 (12 : ZMod 31216151416371941752196801)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 2), (7, 2), (44041, 1), (776057, 1), (11649639971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 2), (7, 2), (44041, 1), (776057, 1), (11649639971, 1)] : List FactorBlock).map factorBlockValue).prod) = 31216151416371941752196801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_7
      · exact prime_eightySevenCG_44041
      · exact prime_eightySevenCG_776057
      · exact prime_eightySevenCG_11649639971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 31216151416371941752196801) ^ 15608075708185970876098400 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (12 : ZMod 31216151416371941752196801) ^ 6243230283274388350439360 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (12 : ZMod 31216151416371941752196801) ^ 4459450202338848821742400 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (12 : ZMod 31216151416371941752196801) ^ 708797516322788804800 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (12 : ZMod 31216151416371941752196801) ^ 40224044646684382400 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (12 : ZMod 31216151416371941752196801) ^ 2679580784820800 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_35677148427660613275576989 : Nat.Prime 35677148427660613275576989 := by
  apply lucas_primality 35677148427660613275576989 (2 : ZMod 35677148427660613275576989)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (114833, 1), (7061073754468072069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (114833, 1), (7061073754468072069, 1)] : List FactorBlock).map factorBlockValue).prod) = 35677148427660613275576989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_11
      · exact prime_eightySevenCG_114833
      · exact prime_eightySevenCG_7061073754468072069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35677148427660613275576989) ^ 17838574213830306637788494 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 35677148427660613275576989) ^ 3243377129787328479597908 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 35677148427660613275576989) ^ 310687245196595171036 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 35677148427660613275576989) ^ 5052652 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_92580755100761069373076921 : Nat.Prime 92580755100761069373076921 := by
  apply lucas_primality 92580755100761069373076921 (14 : ZMod 92580755100761069373076921)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 1), (41, 1), (293, 1), (111341, 1), (21363338100451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 1), (41, 1), (293, 1), (111341, 1), (21363338100451, 1)] : List FactorBlock).map factorBlockValue).prod) = 92580755100761069373076921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_41
      · exact prime_eightySevenCG_293
      · exact prime_eightySevenCG_111341
      · exact prime_eightySevenCG_21363338100451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 92580755100761069373076921) ^ 46290377550380534686538460 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 92580755100761069373076921) ^ 30860251700253689791025640 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 92580755100761069373076921) ^ 18516151020152213874615384 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 92580755100761069373076921) ^ 2258067197579538277392120 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 92580755100761069373076921) ^ 315975273381437096836440 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 92580755100761069373076921) ^ 831506409146325876120 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (14 : ZMod 92580755100761069373076921) ^ 4333627762920 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_197422685061315831235102609 : Nat.Prime 197422685061315831235102609 := by
  apply lucas_primality 197422685061315831235102609 (19 : ZMod 197422685061315831235102609)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (13, 1), (103, 1), (4215697, 1), (26986221891131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (13, 1), (103, 1), (4215697, 1), (26986221891131, 1)] : List FactorBlock).map factorBlockValue).prod) = 197422685061315831235102609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_103
      · exact prime_eightySevenCG_4215697
      · exact prime_eightySevenCG_26986221891131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 197422685061315831235102609) ^ 98711342530657915617551304 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (19 : ZMod 197422685061315831235102609) ^ 65807561687105277078367536 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (19 : ZMod 197422685061315831235102609) ^ 15186360389331987018084816 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (19 : ZMod 197422685061315831235102609) ^ 1916725097682677973156336 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (19 : ZMod 197422685061315831235102609) ^ 46830378241442834064 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (19 : ZMod 197422685061315831235102609) ^ 7315684494768 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_871671346753775831131258129 : Nat.Prime 871671346753775831131258129 := by
  apply lucas_primality 871671346753775831131258129 (7 : ZMod 871671346753775831131258129)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (41, 2), (10802986153502080001131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (41, 2), (10802986153502080001131, 1)] : List FactorBlock).map factorBlockValue).prod) = 871671346753775831131258129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_41
      · exact prime_eightySevenCG_10802986153502080001131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 871671346753775831131258129) ^ 435835673376887915565629064 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 871671346753775831131258129) ^ 290557115584591943710419376 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 871671346753775831131258129) ^ 21260276750092093442225808 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (7 : ZMod 871671346753775831131258129) ^ 80688 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_10285721891694554807348845927 : Nat.Prime 10285721891694554807348845927 := by
  apply lucas_primality 10285721891694554807348845927 (3 : ZMod 10285721891694554807348845927)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1637, 1), (144572738201, 1), (7243499611333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1637, 1), (144572738201, 1), (7243499611333, 1)] : List FactorBlock).map factorBlockValue).prod) = 10285721891694554807348845927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_1637
      · exact prime_eightySevenCG_144572738201
      · exact prime_eightySevenCG_7243499611333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10285721891694554807348845927) ^ 5142860945847277403674422963 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 10285721891694554807348845927) ^ 3428573963898184935782948642 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 10285721891694554807348845927) ^ 6283275437809746369791598 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 10285721891694554807348845927) ^ 71145653182512726 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 10285721891694554807348845927) ^ 1419993434610222 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_20571443783389109614697691841 : Nat.Prime 20571443783389109614697691841 := by
  apply lucas_primality 20571443783389109614697691841 (22 : ZMod 20571443783389109614697691841)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 1), (97, 1), (2267, 1), (10827489627492447719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 1), (97, 1), (2267, 1), (10827489627492447719, 1)] : List FactorBlock).map factorBlockValue).prod) = 20571443783389109614697691841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_97
      · exact prime_eightySevenCG_2267
      · exact prime_eightySevenCG_10827489627492447719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 20571443783389109614697691841) ^ 10285721891694554807348845920 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (22 : ZMod 20571443783389109614697691841) ^ 6857147927796369871565897280 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (22 : ZMod 20571443783389109614697691841) ^ 4114288756677821922939538368 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (22 : ZMod 20571443783389109614697691841) ^ 212076740034939274378326720 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (22 : ZMod 20571443783389109614697691841) ^ 9074302507008870584339520 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (22 : ZMod 20571443783389109614697691841) ^ 1899927360 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_51428609458472774036744229629 : Nat.Prime 51428609458472774036744229629 := by
  apply lucas_primality 51428609458472774036744229629 (2 : ZMod 51428609458472774036744229629)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (3617, 1), (3917, 1), (69466949, 1), (421408014977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (3617, 1), (3917, 1), (69466949, 1), (421408014977, 1)] : List FactorBlock).map factorBlockValue).prod) = 51428609458472774036744229629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_31
      · exact prime_eightySevenCG_3617
      · exact prime_eightySevenCG_3917
      · exact prime_eightySevenCG_69466949
      · exact prime_eightySevenCG_421408014977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51428609458472774036744229629) ^ 25714304729236387018372114814 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 51428609458472774036744229629) ^ 1658987401886218517314329988 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 51428609458472774036744229629) ^ 14218581547822165893487484 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 51428609458472774036744229629) ^ 13129591385875101873051884 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 51428609458472774036744229629) ^ 740332060048769005772 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 51428609458472774036744229629) ^ 122039941412314364 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_102857218916945548073488459201 : Nat.Prime 102857218916945548073488459201 := by
  apply lucas_primality 102857218916945548073488459201 (29 : ZMod 102857218916945548073488459201)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (97, 1), (2267, 1), (10827489627492447719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (97, 1), (2267, 1), (10827489627492447719, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_5
      · exact prime_eightySevenCG_97
      · exact prime_eightySevenCG_2267
      · exact prime_eightySevenCG_10827489627492447719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 102857218916945548073488459201) ^ 51428609458472774036744229600 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (29 : ZMod 102857218916945548073488459201) ^ 34285739638981849357829486400 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (29 : ZMod 102857218916945548073488459201) ^ 20571443783389109614697691840 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (29 : ZMod 102857218916945548073488459201) ^ 1060383700174696371891633600 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (29 : ZMod 102857218916945548073488459201) ^ 45371512535044352921697600 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (29 : ZMod 102857218916945548073488459201) ^ 9499636800 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_102857218916945548073488459217 : Nat.Prime 102857218916945548073488459217 := by
  apply lucas_primality 102857218916945548073488459217 (3 : ZMod 102857218916945548073488459217)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (23, 1), (29, 1), (3119, 1), (181771028626034475961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (23, 1), (29, 1), (3119, 1), (181771028626034475961, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_17
      · exact prime_eightySevenCG_23
      · exact prime_eightySevenCG_29
      · exact prime_eightySevenCG_3119
      · exact prime_eightySevenCG_181771028626034475961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 102857218916945548073488459217) ^ 51428609458472774036744229608 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 102857218916945548073488459217) ^ 6050424642173267533734615248 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 102857218916945548073488459217) ^ 4472052996388936872760367792 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 102857218916945548073488459217) ^ 3546800652308467174947877904 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 102857218916945548073488459217) ^ 32977627097449678766748464 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (3 : ZMod 102857218916945548073488459217) ^ 565861456 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_102857218916945548073488459237 : Nat.Prime 102857218916945548073488459237 := by
  apply lucas_primality 102857218916945548073488459237 (5 : ZMod 102857218916945548073488459237)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (257, 1), (855176584829438525337461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (257, 1), (855176584829438525337461, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_13
      · exact prime_eightySevenCG_257
      · exact prime_eightySevenCG_855176584829438525337461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 102857218916945548073488459237) ^ 51428609458472774036744229618 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 102857218916945548073488459237) ^ 34285739638981849357829486412 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 102857218916945548073488459237) ^ 7912093762841965236422189172 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 102857218916945548073488459237) ^ 400222641700177229857931748 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (5 : ZMod 102857218916945548073488459237) ^ 120276 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_102857218916945548073488459259 : Nat.Prime 102857218916945548073488459259 := by
  apply lucas_primality 102857218916945548073488459259 (2 : ZMod 102857218916945548073488459259)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (51428609458472774036744229629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (51428609458472774036744229629, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_51428609458472774036744229629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 102857218916945548073488459259) ^ 51428609458472774036744229629 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (2 : ZMod 102857218916945548073488459259) ^ 2 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem prime_eightySevenCG_102857218916945548073488459279 : Nat.Prime 102857218916945548073488459279 := by
  apply lucas_primality 102857218916945548073488459279 (6 : ZMod 102857218916945548073488459279)
  · rw [← eightySevenCGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (157, 1), (2833, 1), (3593, 1), (289920122153216453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (157, 1), (2833, 1), (3593, 1), (289920122153216453, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySevenCG_2
      · exact prime_eightySevenCG_3
      · exact prime_eightySevenCG_37
      · exact prime_eightySevenCG_157
      · exact prime_eightySevenCG_2833
      · exact prime_eightySevenCG_3593
      · exact prime_eightySevenCG_289920122153216453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 102857218916945548073488459279) ^ 51428609458472774036744229639 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 102857218916945548073488459279) ^ 34285739638981849357829486426 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 102857218916945548073488459279) ^ 2779924835593122920905093494 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 102857218916945548073488459279) ^ 655141521763984382633684454 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 102857218916945548073488459279) ^ 36306819243538845066533166 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 102857218916945548073488459279) ^ 28627113531017408314358046 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide
    · change (6 : ZMod 102857218916945548073488459279) ^ 354777785526 ≠ 1
      rw [← eightySevenCGFastPow_eq_pow]
      decide

private theorem phi_eightySevenCG_102857218916945548073488459200 : Nat.totient 102857218916945548073488459200 = 27133848387143390670138408960 := by
  rw [← show ((([(2, 6), (3, 3), (5, 2), (97, 1), (2267, 1), (10827489627492447719, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_3, prime_eightySevenCG_5, prime_eightySevenCG_97, prime_eightySevenCG_2267, prime_eightySevenCG_10827489627492447719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459201 : Nat.totient 102857218916945548073488459201 = 102857218916945548073488459200 := by
  rw [← show ((([(102857218916945548073488459201, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_102857218916945548073488459201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459202 : Nat.totient 102857218916945548073488459202 = 51428609458465319134705761732 := by
  rw [← show ((([(2, 1), (6905025521503, 1), (7447997012946367, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_6905025521503, prime_eightySevenCG_7447997012946367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459203 : Nat.totient 102857218916945548073488459203 = 68263983791611948571539101120 := by
  rw [← show ((([(3, 1), (223, 1), (1073660377, 1), (143199576587866231, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_3, prime_eightySevenCG_223, prime_eightySevenCG_1073660377, prime_eightySevenCG_143199576587866231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459204 : Nat.totient 102857218916945548073488459204 = 50038646450091993665952558336 := by
  rw [← show ((([(2, 2), (37, 1), (84727369, 1), (8202558595892204917, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_37, prime_eightySevenCG_84727369, prime_eightySevenCG_8202558595892204917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459205 : Nat.totient 102857218916945548073488459205 = 82285775133556438458790767360 := by
  rw [← show ((([(5, 1), (20571443783389109614697691841, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_5, prime_eightySevenCG_20571443783389109614697691841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459206 : Nat.totient 102857218916945548073488459206 = 29307701147218427866793904576 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (367, 1), (6672973849548822374042329, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_3, prime_eightySevenCG_7, prime_eightySevenCG_367, prime_eightySevenCG_6672973849548822374042329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459207 : Nat.totient 102857218916945548073488459207 = 102737110163564875248452966400 := by
  rw [← show ((([(919, 1), (15641, 1), (63841, 1), (13702859, 1), (8179822507, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_919, prime_eightySevenCG_15641, prime_eightySevenCG_63841, prime_eightySevenCG_13702859, prime_eightySevenCG_8179822507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459208 : Nat.totient 102857218916945548073488459208 = 47923121842205388979871462400 := by
  rw [← show ((([(2, 3), (19, 1), (61, 1), (2549700415441, 1), (4350830856079, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_19, prime_eightySevenCG_61, prime_eightySevenCG_2549700415441, prime_eightySevenCG_4350830856079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459209 : Nat.totient 102857218916945548073488459209 = 62337708423040081274988945120 := by
  rw [← show ((([(3, 2), (11, 1), (5433724573, 1), (191206196280989567, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_3, prime_eightySevenCG_11, prime_eightySevenCG_5433724573, prime_eightySevenCG_191206196280989567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459210 : Nat.totient 102857218916945548073488459210 = 37975324284554095093759082496 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (13933, 1), (2618426137, 1), (21687348619777, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_5, prime_eightySevenCG_13, prime_eightySevenCG_13933, prime_eightySevenCG_2618426137, prime_eightySevenCG_21687348619777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459211 : Nat.totient 102857218916945548073488459211 = 102857218916939679914000584800 := by
  rw [← show ((([(17580691157371, 1), (5850578796717041, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_17580691157371, prime_eightySevenCG_5850578796717041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459212 : Nat.totient 102857218916945548073488459212 = 34280119939839499386123840000 := by
  rw [← show ((([(2, 2), (3, 1), (6101, 1), (4665475621, 1), (301131773646281, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_3, prime_eightySevenCG_6101, prime_eightySevenCG_4665475621, prime_eightySevenCG_301131773646281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459213 : Nat.totient 102857218916945548073488459213 = 88163278156073419835879396400 := by
  rw [← show ((([(7, 1), (1684301, 1), (8724027603561659624759, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_7, prime_eightySevenCG_1684301, prime_eightySevenCG_8724027603561659624759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459214 : Nat.totient 102857218916945548073488459214 = 49767820220562020594109892800 := by
  rw [← show ((([(2, 1), (43, 1), (131, 2), (613, 1), (291840671, 1), (389571740183, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_43, prime_eightySevenCG_131, prime_eightySevenCG_613, prime_eightySevenCG_291840671, prime_eightySevenCG_389571740183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459215 : Nat.totient 102857218916945548073488459215 = 54779490264390195785362053120 := by
  rw [← show ((([(3, 1), (5, 1), (709, 1), (285871, 1), (424913, 1), (79620914995283, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_3, prime_eightySevenCG_5, prime_eightySevenCG_709, prime_eightySevenCG_285871, prime_eightySevenCG_424913, prime_eightySevenCG_79620914995283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459216 : Nat.totient 102857218916945548073488459216 = 44688055478999155912020541440 := by
  rw [← show ((([(2, 4), (17, 1), (23, 1), (29, 1), (3119, 1), (181771028626034475961, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_17, prime_eightySevenCG_23, prime_eightySevenCG_29, prime_eightySevenCG_3119, prime_eightySevenCG_181771028626034475961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459217 : Nat.totient 102857218916945548073488459217 = 102857218916945548073488459216 := by
  rw [← show ((([(102857218916945548073488459217, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_102857218916945548073488459217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459218 : Nat.totient 102857218916945548073488459218 = 33516969499954529896503830400 := by
  rw [← show ((([(2, 1), (3, 2), (53, 1), (277, 1), (78031, 1), (4988149499111548391, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_3, prime_eightySevenCG_53, prime_eightySevenCG_277, prime_eightySevenCG_78031, prime_eightySevenCG_4988149499111548391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459219 : Nat.totient 102857218916945548073488459219 = 102857218423744647683766061296 := by
  rw [← show ((([(208550347, 1), (493200900389513847577, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_208550347, prime_eightySevenCG_493200900389513847577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459220 : Nat.totient 102857218916945548073488459220 = 32028180475293318086939773440 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (11, 1), (1069, 1), (26203, 1), (2384434158119359499, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_5, prime_eightySevenCG_7, prime_eightySevenCG_11, prime_eightySevenCG_1069, prime_eightySevenCG_26203, prime_eightySevenCG_2384434158119359499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459221 : Nat.totient 102857218916945548073488459221 = 67111729738035871861804518720 := by
  rw [← show ((([(3, 1), (47, 1), (97381, 1), (723803, 1), (10349540207697967, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_3, prime_eightySevenCG_47, prime_eightySevenCG_97381, prime_eightySevenCG_723803, prime_eightySevenCG_10349540207697967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459222 : Nat.totient 102857218916945548073488459222 = 50556938111718998205612971424 := by
  rw [← show ((([(2, 1), (59, 1), (871671346753775831131258129, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_59, prime_eightySevenCG_871671346753775831131258129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459223 : Nat.totient 102857218916945548073488459223 = 94945112865144429693461712000 := by
  rw [← show ((([(13, 1), (7726051, 1), (1024079929428625987121, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_13, prime_eightySevenCG_7726051, prime_eightySevenCG_1024079929428625987121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459224 : Nat.totient 102857218916945548073488459224 = 34275165973268688910955774976 := by
  rw [← show ((([(2, 3), (3, 1), (3299, 1), (189473, 1), (6856364360536881763, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_3, prime_eightySevenCG_3299, prime_eightySevenCG_189473, prime_eightySevenCG_6856364360536881763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459225 : Nat.totient 102857218916945548073488459225 = 79570249895784154778954726400 := by
  rw [← show ((([(5, 2), (31, 1), (1597, 1), (11867, 1), (17389, 1), (402728726768309, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_5, prime_eightySevenCG_31, prime_eightySevenCG_1597, prime_eightySevenCG_11867, prime_eightySevenCG_17389, prime_eightySevenCG_402728726768309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459226 : Nat.totient 102857218916945548073488459226 = 51180894165264334587181497600 := by
  rw [← show ((([(2, 1), (359, 1), (491, 1), (5509081, 1), (52960208150271817, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_359, prime_eightySevenCG_491, prime_eightySevenCG_5509081, prime_eightySevenCG_52960208150271817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459227 : Nat.totient 102857218916945548073488459227 = 54319950884562196746721536000 := by
  rw [← show ((([(3, 3), (7, 1), (19, 1), (41, 1), (13417, 1), (15042571, 1), (3461449707031, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_3, prime_eightySevenCG_7, prime_eightySevenCG_19, prime_eightySevenCG_41, prime_eightySevenCG_13417, prime_eightySevenCG_15042571, prime_eightySevenCG_3461449707031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459228 : Nat.totient 102857218916945548073488459228 = 51428609457933884259344714640 := by
  rw [← show ((([(2, 2), (95434409467, 1), (269444793265348021, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_95434409467, prime_eightySevenCG_269444793265348021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459229 : Nat.totient 102857218916945548073488459229 = 102797005667971607831898541440 := by
  rw [← show ((([(1709, 1), (7163017, 1), (7740091, 1), (1085552086123, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_1709, prime_eightySevenCG_7163017, prime_eightySevenCG_7740091, prime_eightySevenCG_1085552086123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459230 : Nat.totient 102857218916945548073488459230 = 27426942458947763250449817600 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (16661, 1), (18012793, 1), (19485097, 1), (586312061, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_3, prime_eightySevenCG_5, prime_eightySevenCG_16661, prime_eightySevenCG_18012793, prime_eightySevenCG_19485097, prime_eightySevenCG_586312061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459231 : Nat.totient 102857218916945548073488459231 = 92580755100761069373076920000 := by
  rw [← show ((([(11, 1), (101, 1), (92580755100761069373076921, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_11, prime_eightySevenCG_101, prime_eightySevenCG_92580755100761069373076921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459232 : Nat.totient 102857218916945548073488459232 = 51428433380735386299949041664 := by
  rw [← show ((([(2, 5), (292079, 1), (11004858586733549407169, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_292079, prime_eightySevenCG_11004858586733549407169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459233 : Nat.totient 102857218916945548073488459233 = 64511600448376567512474681600 := by
  rw [← show ((([(3, 1), (17, 1), (2467, 1), (632851, 1), (1291796136398220499, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_3, prime_eightySevenCG_17, prime_eightySevenCG_2467, prime_eightySevenCG_632851, prime_eightySevenCG_1291796136398220499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459234 : Nat.totient 102857218916945548073488459234 = 44081654991357314028325694976 := by
  rw [← show ((([(2, 1), (7, 2), (4296977, 1), (244256243013676606129, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_7, prime_eightySevenCG_4296977, prime_eightySevenCG_244256243013676606129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459235 : Nat.totient 102857218916945548073488459235 = 82232353632111130552216320000 := by
  rw [← show ((([(5, 1), (3001, 1), (3209, 1), (223211, 1), (9570033710146453, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_5, prime_eightySevenCG_3001, prime_eightySevenCG_3209, prime_eightySevenCG_223211, prime_eightySevenCG_9570033710146453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459236 : Nat.totient 102857218916945548073488459236 = 31525229623152421798040125440 := by
  rw [← show ((([(2, 2), (3, 2), (13, 1), (257, 1), (855176584829438525337461, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_3, prime_eightySevenCG_13, prime_eightySevenCG_257, prime_eightySevenCG_855176584829438525337461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459237 : Nat.totient 102857218916945548073488459237 = 102857218916945548073488459236 := by
  rw [← show ((([(102857218916945548073488459237, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_102857218916945548073488459237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459238 : Nat.totient 102857218916945548073488459238 = 51428609232824654426244565840 := by
  rw [← show ((([(2, 1), (227915081, 1), (225648119610271748699, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_227915081, prime_eightySevenCG_225648119610271748699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459239 : Nat.totient 102857218916945548073488459239 = 65586133646282211277962544128 := by
  rw [← show ((([(3, 1), (23, 1), (16493, 1), (537343399, 1), (168203144180833, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_3, prime_eightySevenCG_23, prime_eightySevenCG_16493, prime_eightySevenCG_537343399, prime_eightySevenCG_168203144180833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459240 : Nat.totient 102857218916945548073488459240 = 40528809141735763259426949120 := by
  rw [← show ((([(2, 3), (5, 1), (67, 1), (7512437, 1), (524811929, 1), (9734540191, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_5, prime_eightySevenCG_67, prime_eightySevenCG_7512437, prime_eightySevenCG_524811929, prime_eightySevenCG_9734540191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459241 : Nat.totient 102857218916945548073488459241 = 84993560373153828963137618880 := by
  rw [← show ((([(7, 1), (37, 1), (109, 1), (3643413939178404876677711, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_7, prime_eightySevenCG_37, prime_eightySevenCG_109, prime_eightySevenCG_3643413939178404876677711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459242 : Nat.totient 102857218916945548073488459242 = 31096536689087990826742697600 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (431, 1), (31674465209, 1), (114157455712403, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_3, prime_eightySevenCG_11, prime_eightySevenCG_431, prime_eightySevenCG_31674465209, prime_eightySevenCG_114157455712403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459243 : Nat.totient 102857218916945548073488459243 = 102774068376114953143063668000 := by
  rw [← show ((([(1237, 1), (1439783588501, 1), (57752110401539, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_1237, prime_eightySevenCG_1439783588501, prime_eightySevenCG_57752110401539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459244 : Nat.totient 102857218916945548073488459244 = 51428540931001450387277483520 := by
  rw [← show ((([(2, 2), (751103, 1), (907214881, 1), (37736804706277, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_751103, prime_eightySevenCG_907214881, prime_eightySevenCG_37736804706277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459245 : Nat.totient 102857218916945548073488459245 = 52965556407162695937326716800 := by
  rw [← show ((([(3, 2), (5, 1), (29, 1), (82284017059, 1), (957874871580551, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_3, prime_eightySevenCG_5, prime_eightySevenCG_29, prime_eightySevenCG_82284017059, prime_eightySevenCG_957874871580551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459246 : Nat.totient 102857218916945548073488459246 = 48721690525163624578397226240 := by
  rw [← show ((([(2, 1), (19, 1), (324781, 1), (8334135675630619116257, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_19, prime_eightySevenCG_324781, prime_eightySevenCG_8334135675630619116257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459247 : Nat.totient 102857218916945548073488459247 = 99204349631779225700678972160 := by
  rw [← show ((([(79, 1), (83, 1), (89, 1), (2288448391, 1), (77019104463029, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_79, prime_eightySevenCG_83, prime_eightySevenCG_89, prime_eightySevenCG_2288448391, prime_eightySevenCG_77019104463029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459248 : Nat.totient 102857218916945548073488459248 = 29308989227961504315080551680 := by
  rw [← show ((([(2, 4), (3, 1), (7, 1), (373, 1), (820704223453223127102391, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_3, prime_eightySevenCG_7, prime_eightySevenCG_373, prime_eightySevenCG_820704223453223127102391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459249 : Nat.totient 102857218916945548073488459249 = 94941155377397994539520502080 := by
  rw [← show ((([(13, 1), (23917, 1), (95994553631, 1), (3446181353399, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_13, prime_eightySevenCG_23917, prime_eightySevenCG_95994553631, prime_eightySevenCG_3446181353399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459250 : Nat.totient 102857218916945548073488459250 = 38722717709439540701209600000 := by
  rw [← show ((([(2, 1), (5, 3), (17, 1), (82522292861, 1), (293274674389601, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_5, prime_eightySevenCG_17, prime_eightySevenCG_82522292861, prime_eightySevenCG_293274674389601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459251 : Nat.totient 102857218916945548073488459251 = 68392376546126766223564032000 := by
  rw [← show ((([(3, 1), (401, 1), (8599, 1), (465041, 1), (21381095702732663, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_3, prime_eightySevenCG_401, prime_eightySevenCG_8599, prime_eightySevenCG_465041, prime_eightySevenCG_21381095702732663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459252 : Nat.totient 102857218916945548073488459252 = 50863398031494635865801915392 := by
  rw [← show ((([(2, 2), (137, 1), (269, 1), (1630133, 1), (428034623037428837, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_137, prime_eightySevenCG_269, prime_eightySevenCG_1630133, prime_eightySevenCG_428034623037428837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459253 : Nat.totient 102857218916945548073488459253 = 93506555292935804134531063200 := by
  rw [← show ((([(11, 1), (12706711, 1), (735883287593214955993, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_11, prime_eightySevenCG_12706711, prime_eightySevenCG_735883287593214955993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459254 : Nat.totient 102857218916945548073488459254 = 34270994413416432948538429440 := by
  rw [← show ((([(2, 1), (3, 4), (2731, 1), (23857, 1), (45433, 1), (214491861107897, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_3, prime_eightySevenCG_2731, prime_eightySevenCG_23857, prime_eightySevenCG_45433, prime_eightySevenCG_214491861107897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459255 : Nat.totient 102857218916945548073488459255 = 69719932771641779653031846400 := by
  rw [← show ((([(5, 1), (7, 1), (107, 1), (461, 1), (47549279, 1), (1252962560464621, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_5, prime_eightySevenCG_7, prime_eightySevenCG_107, prime_eightySevenCG_461, prime_eightySevenCG_47549279, prime_eightySevenCG_1252962560464621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459256 : Nat.totient 102857218916945548073488459256 = 49743158879463756788528578560 := by
  rw [← show ((([(2, 3), (31, 1), (3617, 1), (3917, 1), (69466949, 1), (421408014977, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_31, prime_eightySevenCG_3617, prime_eightySevenCG_3917, prime_eightySevenCG_69466949, prime_eightySevenCG_421408014977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459257 : Nat.totient 102857218916945548073488459257 = 66494942484759062383729820256 := by
  rw [← show ((([(3, 1), (43, 2), (139, 1), (17536447, 1), (7607118900831007, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_3, prime_eightySevenCG_43, prime_eightySevenCG_139, prime_eightySevenCG_17536447, prime_eightySevenCG_7607118900831007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459258 : Nat.totient 102857218916945548073488459258 = 51428609458472774036744229628 := by
  rw [← show ((([(2, 1), (51428609458472774036744229629, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_51428609458472774036744229629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459259 : Nat.totient 102857218916945548073488459259 = 102857218916945548073488459258 := by
  rw [← show ((([(102857218916945548073488459259, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_102857218916945548073488459259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459260 : Nat.totient 102857218916945548073488459260 = 27411836309824596647456102400 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (1637, 1), (144572738201, 1), (7243499611333, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_3, prime_eightySevenCG_5, prime_eightySevenCG_1637, prime_eightySevenCG_144572738201, prime_eightySevenCG_7243499611333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459261 : Nat.totient 102857218916945548073488459261 = 101946972908416796023661199360 := by
  rw [← show ((([(113, 1), (19860481, 1), (45831763861670799437, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_113, prime_eightySevenCG_19860481, prime_eightySevenCG_45831763861670799437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459262 : Nat.totient 102857218916945548073488459262 = 38921603923690247483723197440 := by
  rw [← show ((([(2, 1), (7, 1), (13, 1), (23, 2), (220207441, 1), (4851496556629069, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_7, prime_eightySevenCG_13, prime_eightySevenCG_23, prime_eightySevenCG_220207441, prime_eightySevenCG_4851496556629069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459263 : Nat.totient 102857218916945548073488459263 = 67022263550728717909308933120 := by
  rw [← show ((([(3, 2), (73, 1), (163, 1), (599, 1), (811, 1), (1977124997128183337, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_3, prime_eightySevenCG_73, prime_eightySevenCG_163, prime_eightySevenCG_599, prime_eightySevenCG_811, prime_eightySevenCG_1977124997128183337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459264 : Nat.totient 102857218916945548073488459264 = 46753277480044927374621542400 := by
  rw [← show ((([(2, 9), (11, 1), (12156847, 1), (1502281020557679991, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_11, prime_eightySevenCG_12156847, prime_eightySevenCG_1502281020557679991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459265 : Nat.totient 102857218916945548073488459265 = 77954298958166190404737942080 := by
  rw [← show ((([(5, 1), (19, 1), (120691, 1), (8970905598153924011557, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_5, prime_eightySevenCG_19, prime_eightySevenCG_120691, prime_eightySevenCG_8970905598153924011557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459266 : Nat.totient 102857218916945548073488459266 = 34263513913606262864680194000 := by
  rw [← show ((([(2, 1), (3, 1), (1543, 1), (6180127, 1), (1797712347230697251, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_3, prime_eightySevenCG_1543, prime_eightySevenCG_6180127, prime_eightySevenCG_1797712347230697251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459267 : Nat.totient 102857218916945548073488459267 = 96806608074559021683295160832 := by
  rw [← show ((([(17, 1), (519907, 1), (11637513328678528147793, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_17, prime_eightySevenCG_519907, prime_eightySevenCG_11637513328678528147793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459268 : Nat.totient 102857218916945548073488459268 = 48415071911319823760497843200 := by
  rw [← show ((([(2, 2), (41, 1), (47, 1), (71, 1), (1452569653, 1), (129389119118317, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_41, prime_eightySevenCG_47, prime_eightySevenCG_71, prime_eightySevenCG_1452569653, prime_eightySevenCG_129389119118317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459269 : Nat.totient 102857218916945548073488459269 = 57796098210016247987902180800 := by
  rw [← show ((([(3, 1), (7, 1), (61, 1), (3631, 1), (22113597417361588608779, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_3, prime_eightySevenCG_7, prime_eightySevenCG_61, prime_eightySevenCG_3631, prime_eightySevenCG_22113597417361588608779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459270 : Nat.totient 102857218916945548073488459270 = 41142887566778219229395383704 := by
  rw [← show ((([(2, 1), (5, 1), (10285721891694554807348845927, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_5, prime_eightySevenCG_10285721891694554807348845927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459271 : Nat.totient 102857218916945548073488459271 = 100570052794752629365729795200 := by
  rw [← show ((([(53, 1), (397, 1), (1091, 1), (4480677130993804905341, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_53, prime_eightySevenCG_397, prime_eightySevenCG_1091, prime_eightySevenCG_4480677130993804905341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459272 : Nat.totient 102857218916945548073488459272 = 34280490719036768106805107840 := by
  rw [← show ((([(2, 3), (3, 2), (12799, 1), (13339, 1), (8367639656874110341, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_3, prime_eightySevenCG_12799, prime_eightySevenCG_13339, prime_eightySevenCG_8367639656874110341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459273 : Nat.totient 102857218916945548073488459273 = 102047319555324984178956760464 := by
  rw [← show ((([(127, 1), (1465631125853, 1), (552594269638883, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_127, prime_eightySevenCG_1465631125853, prime_eightySevenCG_552594269638883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459274 : Nat.totient 102857218916945548073488459274 = 49449739894378862243312959488 := by
  rw [← show ((([(2, 1), (29, 1), (337, 1), (1153, 1), (3259, 1), (6064703, 1), (230915814949, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_29, prime_eightySevenCG_337, prime_eightySevenCG_1153, prime_eightySevenCG_3259, prime_eightySevenCG_6064703, prime_eightySevenCG_230915814949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459275 : Nat.totient 102857218916945548073488459275 = 45832978240329478654165248000 := by
  rw [← show ((([(3, 1), (5, 2), (11, 2), (13, 1), (229, 1), (3807231711882765039721, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_3, prime_eightySevenCG_5, prime_eightySevenCG_11, prime_eightySevenCG_13, prime_eightySevenCG_229, prime_eightySevenCG_3807231711882765039721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459276 : Nat.totient 102857218916945548073488459276 = 44080868675095575112028602512 := by
  rw [← show ((([(2, 2), (7, 1), (55339, 1), (66381251995457574529903, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_7, prime_eightySevenCG_55339, prime_eightySevenCG_66381251995457574529903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459277 : Nat.totient 102857218916945548073488459277 = 102853825743469832535154814208 := by
  rw [← show ((([(30313, 1), (64161055373, 1), (52885225328473, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_30313, prime_eightySevenCG_64161055373, prime_eightySevenCG_52885225328473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459278 : Nat.totient 102857218916945548073488459278 = 33125697436167300925515350016 := by
  rw [← show ((([(2, 1), (3, 1), (37, 1), (157, 1), (2833, 1), (3593, 1), (289920122153216453, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_3, prime_eightySevenCG_37, prime_eightySevenCG_157, prime_eightySevenCG_2833, prime_eightySevenCG_3593, prime_eightySevenCG_289920122153216453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459279 : Nat.totient 102857218916945548073488459279 = 102857218916945548073488459278 := by
  rw [← show ((([(102857218916945548073488459279, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_102857218916945548073488459279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459280 : Nat.totient 102857218916945548073488459280 = 40866760804557089485470835200 := by
  rw [← show ((([(2, 4), (5, 1), (149, 1), (2636075560759, 1), (3273411979151, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_5, prime_eightySevenCG_149, prime_eightySevenCG_2636075560759, prime_eightySevenCG_3273411979151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459281 : Nat.totient 102857218916945548073488459281 = 67339828312210680754471465680 := by
  rw [← show ((([(3, 3), (59, 1), (971, 1), (66496650780316270445227, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_3, prime_eightySevenCG_59, prime_eightySevenCG_971, prime_eightySevenCG_66496650780316270445227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459282 : Nat.totient 102857218916945548073488459282 = 51428584829796851985407375472 := by
  rw [← show ((([(2, 1), (2088343, 1), (24369198883, 1), (1010559056789, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_2088343, prime_eightySevenCG_24369198883, prime_eightySevenCG_1010559056789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459283 : Nat.totient 102857218916945548073488459283 = 87194429682749382191579807328 := by
  rw [← show ((([(7, 3), (103, 1), (773, 1), (3766378299279529695799, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_7, prime_eightySevenCG_103, prime_eightySevenCG_773, prime_eightySevenCG_3766378299279529695799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459284 : Nat.totient 102857218916945548073488459284 = 30570555466371536624786001408 := by
  rw [← show ((([(2, 2), (3, 1), (17, 1), (19, 1), (2742563, 1), (9675967401649650943, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_3, prime_eightySevenCG_17, prime_eightySevenCG_19, prime_eightySevenCG_2742563, prime_eightySevenCG_9675967401649650943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459285 : Nat.totient 102857218916945548073488459285 = 78681515173801918893297606208 := by
  rw [← show ((([(5, 1), (23, 1), (2957, 1), (302472302765568946415987, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_5, prime_eightySevenCG_23, prime_eightySevenCG_2957, prime_eightySevenCG_302472302765568946415987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459286 : Nat.totient 102857218916945548073488459286 = 46603909820050843739367408000 := by
  rw [← show ((([(2, 1), (11, 1), (313, 1), (14937150583349629403643401, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_11, prime_eightySevenCG_313, prime_eightySevenCG_14937150583349629403643401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459287 : Nat.totient 102857218916945548073488459287 = 66359496075448740692573197680 := by
  rw [← show ((([(3, 1), (31, 2), (35677148427660613275576989, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_3, prime_eightySevenCG_31, prime_eightySevenCG_35677148427660613275576989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459288 : Nat.totient 102857218916945548073488459288 = 47328978467358669739895170560 := by
  rw [← show ((([(2, 3), (13, 1), (331, 1), (292309, 1), (85225979, 1), (119938678267, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_13, prime_eightySevenCG_331, prime_eightySevenCG_292309, prime_eightySevenCG_85225979, prime_eightySevenCG_119938678267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459289 : Nat.totient 102857218916945548073488459289 = 102659796231884232242253356160 := by
  rw [← show ((([(521, 1), (197422685061315831235102609, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_521, prime_eightySevenCG_197422685061315831235102609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459290 : Nat.totient 102857218916945548073488459290 = 23380330740394883855694272640 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (7, 1), (181, 1), (902018932885605087025243, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_3, prime_eightySevenCG_5, prime_eightySevenCG_7, prime_eightySevenCG_181, prime_eightySevenCG_902018932885605087025243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459291 : Nat.totient 102857218916945548073488459291 = 102857200543413489011224971784 := by
  rw [← show ((([(5598119, 1), (18373532059062257889389, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_5598119, prime_eightySevenCG_18373532059062257889389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459292 : Nat.totient 102857218916945548073488459292 = 51103724966714091008440880640 := by
  rw [← show ((([(2, 2), (293, 1), (347, 1), (33647, 1), (370471, 1), (20289770061049, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_293, prime_eightySevenCG_347, prime_eightySevenCG_33647, prime_eightySevenCG_370471, prime_eightySevenCG_20289770061049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459293 : Nat.totient 102857218916945548073488459293 = 68571356918696521655074252400 := by
  rw [← show ((([(3, 1), (560411, 1), (61179633588530291799821, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_3, prime_eightySevenCG_560411, prime_eightySevenCG_61179633588530291799821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459294 : Nat.totient 102857218916945548073488459294 = 51428572490397605506998553728 := by
  rw [← show ((([(2, 1), (1391183, 1), (173282436553, 1), (213336896953, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_1391183, prime_eightySevenCG_173282436553, prime_eightySevenCG_213336896953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459295 : Nat.totient 102857218916945548073488459295 = 82160910527890950691781977600 := by
  rw [← show ((([(5, 1), (659, 1), (31216151416371941752196801, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_5, prime_eightySevenCG_659, prime_eightySevenCG_31216151416371941752196801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459296 : Nat.totient 102857218916945548073488459296 = 34285739638914190270590652928 := by
  rw [← show ((([(2, 5), (3, 1), (506864076899, 1), (2113839612136649, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_3, prime_eightySevenCG_506864076899, prime_eightySevenCG_2113839612136649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459297 : Nat.totient 102857218916945548073488459297 = 79191528536363541090135091200 := by
  rw [← show ((([(7, 1), (11, 1), (97, 1), (607, 1), (48560741, 1), (467195145972799, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_7, prime_eightySevenCG_11, prime_eightySevenCG_97, prime_eightySevenCG_607, prime_eightySevenCG_48560741, prime_eightySevenCG_467195145972799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459298 : Nat.totient 102857218916945548073488459298 = 51282919344475380559549094400 := by
  rw [← show ((([(2, 1), (353, 1), (23131577101, 1), (6298321603591733, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_353, prime_eightySevenCG_23131577101, prime_eightySevenCG_6298321603591733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459299 : Nat.totient 102857218916945548073488459299 = 68571479277776576529068644944 := by
  rw [← show ((([(3, 2), (366457266629, 1), (31186664641121359, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_3, prime_eightySevenCG_366457266629, prime_eightySevenCG_31186664641121359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459300 : Nat.totient 102857218916945548073488459300 = 40178132742548161550323330560 := by
  rw [← show ((([(2, 2), (5, 2), (43, 1), (5059, 1), (12535721053, 1), (377183184613, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_2, prime_eightySevenCG_5, prime_eightySevenCG_43, prime_eightySevenCG_5059, prime_eightySevenCG_12535721053, prime_eightySevenCG_377183184613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySevenCG_102857218916945548073488459301 : Nat.totient 102857218916945548073488459301 = 89358481118105420849545881600 := by
  rw [← show ((([(13, 2), (17, 1), (54601, 1), (1247981699, 1), (525400326263, 1)] : List FactorBlock).map factorBlockValue).prod) = 102857218916945548073488459301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySevenCG_13, prime_eightySevenCG_17, prime_eightySevenCG_54601, prime_eightySevenCG_1247981699, prime_eightySevenCG_525400326263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64EightySevenCG : certifiedKill 1 102857218916945548073488459199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_eightySevenCG_102857218916945548073488459200, phi_eightySevenCG_102857218916945548073488459201, phi_eightySevenCG_102857218916945548073488459202,
    phi_eightySevenCG_102857218916945548073488459203, phi_eightySevenCG_102857218916945548073488459204, phi_eightySevenCG_102857218916945548073488459205,
    phi_eightySevenCG_102857218916945548073488459206, phi_eightySevenCG_102857218916945548073488459207, phi_eightySevenCG_102857218916945548073488459208,
    phi_eightySevenCG_102857218916945548073488459209, phi_eightySevenCG_102857218916945548073488459210, phi_eightySevenCG_102857218916945548073488459211,
    phi_eightySevenCG_102857218916945548073488459212, phi_eightySevenCG_102857218916945548073488459213, phi_eightySevenCG_102857218916945548073488459214,
    phi_eightySevenCG_102857218916945548073488459215, phi_eightySevenCG_102857218916945548073488459216, phi_eightySevenCG_102857218916945548073488459217,
    phi_eightySevenCG_102857218916945548073488459218, phi_eightySevenCG_102857218916945548073488459219, phi_eightySevenCG_102857218916945548073488459220,
    phi_eightySevenCG_102857218916945548073488459221, phi_eightySevenCG_102857218916945548073488459222, phi_eightySevenCG_102857218916945548073488459223,
    phi_eightySevenCG_102857218916945548073488459224, phi_eightySevenCG_102857218916945548073488459225, phi_eightySevenCG_102857218916945548073488459226,
    phi_eightySevenCG_102857218916945548073488459227, phi_eightySevenCG_102857218916945548073488459228, phi_eightySevenCG_102857218916945548073488459229,
    phi_eightySevenCG_102857218916945548073488459230, phi_eightySevenCG_102857218916945548073488459231, phi_eightySevenCG_102857218916945548073488459232,
    phi_eightySevenCG_102857218916945548073488459233, phi_eightySevenCG_102857218916945548073488459234, phi_eightySevenCG_102857218916945548073488459235,
    phi_eightySevenCG_102857218916945548073488459236, phi_eightySevenCG_102857218916945548073488459237, phi_eightySevenCG_102857218916945548073488459238,
    phi_eightySevenCG_102857218916945548073488459239, phi_eightySevenCG_102857218916945548073488459240, phi_eightySevenCG_102857218916945548073488459241,
    phi_eightySevenCG_102857218916945548073488459242, phi_eightySevenCG_102857218916945548073488459243, phi_eightySevenCG_102857218916945548073488459244,
    phi_eightySevenCG_102857218916945548073488459245, phi_eightySevenCG_102857218916945548073488459246, phi_eightySevenCG_102857218916945548073488459247,
    phi_eightySevenCG_102857218916945548073488459248, phi_eightySevenCG_102857218916945548073488459249, phi_eightySevenCG_102857218916945548073488459250,
    phi_eightySevenCG_102857218916945548073488459251, phi_eightySevenCG_102857218916945548073488459252, phi_eightySevenCG_102857218916945548073488459253,
    phi_eightySevenCG_102857218916945548073488459254, phi_eightySevenCG_102857218916945548073488459255, phi_eightySevenCG_102857218916945548073488459256,
    phi_eightySevenCG_102857218916945548073488459257, phi_eightySevenCG_102857218916945548073488459258, phi_eightySevenCG_102857218916945548073488459259,
    phi_eightySevenCG_102857218916945548073488459260, phi_eightySevenCG_102857218916945548073488459261, phi_eightySevenCG_102857218916945548073488459262,
    phi_eightySevenCG_102857218916945548073488459263, phi_eightySevenCG_102857218916945548073488459264, phi_eightySevenCG_102857218916945548073488459265,
    phi_eightySevenCG_102857218916945548073488459266, phi_eightySevenCG_102857218916945548073488459267, phi_eightySevenCG_102857218916945548073488459268,
    phi_eightySevenCG_102857218916945548073488459269, phi_eightySevenCG_102857218916945548073488459270, phi_eightySevenCG_102857218916945548073488459271,
    phi_eightySevenCG_102857218916945548073488459272, phi_eightySevenCG_102857218916945548073488459273, phi_eightySevenCG_102857218916945548073488459274,
    phi_eightySevenCG_102857218916945548073488459275, phi_eightySevenCG_102857218916945548073488459276, phi_eightySevenCG_102857218916945548073488459277,
    phi_eightySevenCG_102857218916945548073488459278, phi_eightySevenCG_102857218916945548073488459279, phi_eightySevenCG_102857218916945548073488459280,
    phi_eightySevenCG_102857218916945548073488459281, phi_eightySevenCG_102857218916945548073488459282, phi_eightySevenCG_102857218916945548073488459283,
    phi_eightySevenCG_102857218916945548073488459284, phi_eightySevenCG_102857218916945548073488459285, phi_eightySevenCG_102857218916945548073488459286,
    phi_eightySevenCG_102857218916945548073488459287, phi_eightySevenCG_102857218916945548073488459288, phi_eightySevenCG_102857218916945548073488459289,
    phi_eightySevenCG_102857218916945548073488459290, phi_eightySevenCG_102857218916945548073488459291, phi_eightySevenCG_102857218916945548073488459292,
    phi_eightySevenCG_102857218916945548073488459293, phi_eightySevenCG_102857218916945548073488459294, phi_eightySevenCG_102857218916945548073488459295,
    phi_eightySevenCG_102857218916945548073488459296, phi_eightySevenCG_102857218916945548073488459297, phi_eightySevenCG_102857218916945548073488459298,
    phi_eightySevenCG_102857218916945548073488459299, phi_eightySevenCG_102857218916945548073488459300, phi_eightySevenCG_102857218916945548073488459301
    ]

end TotientTailPeriodKiller
end Erdos249257
