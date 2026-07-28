import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredSixtyTwoFDFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredSixtyTwoFDFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredSixtyTwoFDFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredSixtyTwoFDFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredSixtyTwoFDFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredSixtyTwoFDFastPow a n * oneHundredSixtyTwoFDFastPow a n * a else oneHundredSixtyTwoFDFastPow a n * oneHundredSixtyTwoFDFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredSixtyTwoFD_2 : Nat.Prime 2 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_3 : Nat.Prime 3 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_5 : Nat.Prime 5 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_7 : Nat.Prime 7 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_11 : Nat.Prime 11 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_13 : Nat.Prime 13 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_17 : Nat.Prime 17 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_19 : Nat.Prime 19 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_23 : Nat.Prime 23 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_29 : Nat.Prime 29 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_31 : Nat.Prime 31 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_37 : Nat.Prime 37 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_41 : Nat.Prime 41 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_43 : Nat.Prime 43 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_47 : Nat.Prime 47 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_53 : Nat.Prime 53 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_59 : Nat.Prime 59 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_61 : Nat.Prime 61 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_67 : Nat.Prime 67 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_71 : Nat.Prime 71 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_73 : Nat.Prime 73 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_79 : Nat.Prime 79 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_83 : Nat.Prime 83 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_89 : Nat.Prime 89 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_97 : Nat.Prime 97 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_101 : Nat.Prime 101 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_103 : Nat.Prime 103 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_107 : Nat.Prime 107 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_109 : Nat.Prime 109 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_113 : Nat.Prime 113 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_127 : Nat.Prime 127 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_131 : Nat.Prime 131 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_137 : Nat.Prime 137 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_139 : Nat.Prime 139 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_149 : Nat.Prime 149 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_151 : Nat.Prime 151 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_157 : Nat.Prime 157 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_163 : Nat.Prime 163 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_167 : Nat.Prime 167 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_173 : Nat.Prime 173 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_181 : Nat.Prime 181 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_191 : Nat.Prime 191 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_193 : Nat.Prime 193 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_197 : Nat.Prime 197 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_199 : Nat.Prime 199 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_211 : Nat.Prime 211 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_223 : Nat.Prime 223 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_227 : Nat.Prime 227 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_229 : Nat.Prime 229 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_233 : Nat.Prime 233 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_239 : Nat.Prime 239 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_241 : Nat.Prime 241 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_251 : Nat.Prime 251 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_257 : Nat.Prime 257 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_263 : Nat.Prime 263 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_271 : Nat.Prime 271 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_277 : Nat.Prime 277 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_283 : Nat.Prime 283 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_293 : Nat.Prime 293 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_307 : Nat.Prime 307 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_311 : Nat.Prime 311 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_313 : Nat.Prime 313 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_317 : Nat.Prime 317 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_347 : Nat.Prime 347 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_349 : Nat.Prime 349 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_367 : Nat.Prime 367 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_373 : Nat.Prime 373 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_379 : Nat.Prime 379 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_383 : Nat.Prime 383 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_389 : Nat.Prime 389 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_401 : Nat.Prime 401 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_419 : Nat.Prime 419 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_431 : Nat.Prime 431 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_439 : Nat.Prime 439 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_457 : Nat.Prime 457 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_461 : Nat.Prime 461 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_463 : Nat.Prime 463 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_499 : Nat.Prime 499 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_523 : Nat.Prime 523 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_541 : Nat.Prime 541 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_563 : Nat.Prime 563 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_569 : Nat.Prime 569 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_613 : Nat.Prime 613 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_631 : Nat.Prime 631 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_641 : Nat.Prime 641 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_647 : Nat.Prime 647 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_673 : Nat.Prime 673 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_691 : Nat.Prime 691 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_701 : Nat.Prime 701 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_719 : Nat.Prime 719 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_761 : Nat.Prime 761 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_797 : Nat.Prime 797 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_827 : Nat.Prime 827 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_839 : Nat.Prime 839 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_857 : Nat.Prime 857 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_907 : Nat.Prime 907 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_911 : Nat.Prime 911 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_937 : Nat.Prime 937 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_967 : Nat.Prime 967 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1009 : Nat.Prime 1009 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1033 : Nat.Prime 1033 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1039 : Nat.Prime 1039 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1049 : Nat.Prime 1049 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1069 : Nat.Prime 1069 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1097 : Nat.Prime 1097 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1153 : Nat.Prime 1153 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1193 : Nat.Prime 1193 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1217 : Nat.Prime 1217 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1229 : Nat.Prime 1229 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1297 : Nat.Prime 1297 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1367 : Nat.Prime 1367 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1381 : Nat.Prime 1381 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1409 : Nat.Prime 1409 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1493 : Nat.Prime 1493 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1511 : Nat.Prime 1511 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1523 : Nat.Prime 1523 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1553 : Nat.Prime 1553 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1579 : Nat.Prime 1579 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1583 : Nat.Prime 1583 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1597 : Nat.Prime 1597 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1609 : Nat.Prime 1609 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1637 : Nat.Prime 1637 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1657 : Nat.Prime 1657 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1699 : Nat.Prime 1699 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1811 : Nat.Prime 1811 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1823 : Nat.Prime 1823 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1831 : Nat.Prime 1831 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1847 : Nat.Prime 1847 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1889 : Nat.Prime 1889 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1951 : Nat.Prime 1951 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2011 : Nat.Prime 2011 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2027 : Nat.Prime 2027 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2053 : Nat.Prime 2053 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2063 : Nat.Prime 2063 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2267 : Nat.Prime 2267 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2341 : Nat.Prime 2341 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2411 : Nat.Prime 2411 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2441 : Nat.Prime 2441 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2549 : Nat.Prime 2549 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2551 : Nat.Prime 2551 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2593 : Nat.Prime 2593 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2659 : Nat.Prime 2659 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2699 : Nat.Prime 2699 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2707 : Nat.Prime 2707 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2741 : Nat.Prime 2741 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2801 : Nat.Prime 2801 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2819 : Nat.Prime 2819 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2879 : Nat.Prime 2879 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2903 : Nat.Prime 2903 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2927 : Nat.Prime 2927 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2939 : Nat.Prime 2939 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2963 : Nat.Prime 2963 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_3251 : Nat.Prime 3251 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_3413 : Nat.Prime 3413 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_3433 : Nat.Prime 3433 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_3527 : Nat.Prime 3527 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_3607 : Nat.Prime 3607 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_3637 : Nat.Prime 3637 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_3697 : Nat.Prime 3697 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_3701 : Nat.Prime 3701 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_3917 : Nat.Prime 3917 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4007 : Nat.Prime 4007 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4289 : Nat.Prime 4289 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4421 : Nat.Prime 4421 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4423 : Nat.Prime 4423 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4561 : Nat.Prime 4561 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4673 : Nat.Prime 4673 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4703 : Nat.Prime 4703 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4723 : Nat.Prime 4723 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4733 : Nat.Prime 4733 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4799 : Nat.Prime 4799 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4817 : Nat.Prime 4817 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4871 : Nat.Prime 4871 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4999 : Nat.Prime 4999 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_5087 : Nat.Prime 5087 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_5171 : Nat.Prime 5171 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_5323 : Nat.Prime 5323 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_5783 : Nat.Prime 5783 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_5881 : Nat.Prime 5881 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_6011 : Nat.Prime 6011 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_6173 : Nat.Prime 6173 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_6287 : Nat.Prime 6287 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_6427 : Nat.Prime 6427 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_6829 : Nat.Prime 6829 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_6863 : Nat.Prime 6863 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_7019 : Nat.Prime 7019 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_7039 : Nat.Prime 7039 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_7127 : Nat.Prime 7127 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_7213 : Nat.Prime 7213 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_7349 : Nat.Prime 7349 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_7481 : Nat.Prime 7481 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_7547 : Nat.Prime 7547 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_7573 : Nat.Prime 7573 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_8273 : Nat.Prime 8273 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_8573 : Nat.Prime 8573 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_8641 : Nat.Prime 8641 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_10289 : Nat.Prime 10289 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_10501 : Nat.Prime 10501 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_13693 : Nat.Prime 13693 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_14033 : Nat.Prime 14033 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_14779 : Nat.Prime 14779 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_15121 : Nat.Prime 15121 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_15737 : Nat.Prime 15737 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_16111 : Nat.Prime 16111 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_17203 : Nat.Prime 17203 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_18701 : Nat.Prime 18701 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_19141 : Nat.Prime 19141 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_19421 : Nat.Prime 19421 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_19813 : Nat.Prime 19813 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_19973 : Nat.Prime 19973 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_20029 : Nat.Prime 20029 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_20113 : Nat.Prime 20113 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_20681 : Nat.Prime 20681 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_20753 : Nat.Prime 20753 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_21577 : Nat.Prime 21577 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_21617 : Nat.Prime 21617 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_21683 : Nat.Prime 21683 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_22817 : Nat.Prime 22817 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_22901 : Nat.Prime 22901 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_23929 : Nat.Prime 23929 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_24181 : Nat.Prime 24181 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_24337 : Nat.Prime 24337 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_24749 : Nat.Prime 24749 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_24907 : Nat.Prime 24907 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_25117 : Nat.Prime 25117 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_27067 : Nat.Prime 27067 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_28403 : Nat.Prime 28403 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_28933 : Nat.Prime 28933 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_29437 : Nat.Prime 29437 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_29501 : Nat.Prime 29501 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_30671 : Nat.Prime 30671 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_30727 : Nat.Prime 30727 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_31177 : Nat.Prime 31177 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_32363 : Nat.Prime 32363 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_33911 : Nat.Prime 33911 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_34273 : Nat.Prime 34273 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_36781 : Nat.Prime 36781 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_37693 : Nat.Prime 37693 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_37987 : Nat.Prime 37987 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_39821 : Nat.Prime 39821 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_40487 : Nat.Prime 40487 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_42379 : Nat.Prime 42379 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_44987 : Nat.Prime 44987 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_47279 : Nat.Prime 47279 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_48017 : Nat.Prime 48017 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_48571 : Nat.Prime 48571 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_49531 : Nat.Prime 49531 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_49613 : Nat.Prime 49613 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_49727 : Nat.Prime 49727 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_52067 : Nat.Prime 52067 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_53147 : Nat.Prime 53147 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_57709 : Nat.Prime 57709 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_59149 : Nat.Prime 59149 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_59509 : Nat.Prime 59509 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_62801 : Nat.Prime 62801 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_65809 : Nat.Prime 65809 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_66373 : Nat.Prime 66373 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_66959 : Nat.Prime 66959 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_69959 : Nat.Prime 69959 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_69997 : Nat.Prime 69997 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_70583 : Nat.Prime 70583 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_70709 : Nat.Prime 70709 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_71209 : Nat.Prime 71209 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_74257 : Nat.Prime 74257 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_74383 : Nat.Prime 74383 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_74687 : Nat.Prime 74687 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_79423 : Nat.Prime 79423 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_79847 : Nat.Prime 79847 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_80317 : Nat.Prime 80317 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_82469 : Nat.Prime 82469 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_82811 : Nat.Prime 82811 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_84313 : Nat.Prime 84313 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_84389 : Nat.Prime 84389 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_85621 : Nat.Prime 85621 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_86629 : Nat.Prime 86629 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_86729 : Nat.Prime 86729 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_89833 : Nat.Prime 89833 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_93419 : Nat.Prime 93419 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_98507 : Nat.Prime 98507 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_99137 : Nat.Prime 99137 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_99871 : Nat.Prime 99871 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_109891 : Nat.Prime 109891 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_110233 : Nat.Prime 110233 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_111103 : Nat.Prime 111103 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_114967 : Nat.Prime 114967 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_121697 : Nat.Prime 121697 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_122251 : Nat.Prime 122251 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_122701 : Nat.Prime 122701 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_125287 : Nat.Prime 125287 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_125813 : Nat.Prime 125813 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_126719 : Nat.Prime 126719 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_127681 : Nat.Prime 127681 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_143333 : Nat.Prime 143333 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_147391 : Nat.Prime 147391 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_150203 : Nat.Prime 150203 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_154159 : Nat.Prime 154159 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_154937 : Nat.Prime 154937 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_160093 : Nat.Prime 160093 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_160907 : Nat.Prime 160907 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_161957 : Nat.Prime 161957 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_165833 : Nat.Prime 165833 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_171401 : Nat.Prime 171401 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_188911 : Nat.Prime 188911 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_191911 : Nat.Prime 191911 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_192791 : Nat.Prime 192791 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_211231 : Nat.Prime 211231 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_212467 : Nat.Prime 212467 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_212557 : Nat.Prime 212557 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_221069 : Nat.Prime 221069 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_233341 : Nat.Prime 233341 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_278701 : Nat.Prime 278701 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_284833 : Nat.Prime 284833 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_285697 : Nat.Prime 285697 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_288689 : Nat.Prime 288689 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_296987 : Nat.Prime 296987 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_300331 : Nat.Prime 300331 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_310313 : Nat.Prime 310313 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_319259 : Nat.Prime 319259 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_364879 : Nat.Prime 364879 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_374111 : Nat.Prime 374111 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_388373 : Nat.Prime 388373 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_392927 : Nat.Prime 392927 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_396547 : Nat.Prime 396547 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_408347 : Nat.Prime 408347 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_420241 : Nat.Prime 420241 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_438467 : Nat.Prime 438467 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_444539 : Nat.Prime 444539 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_474571 : Nat.Prime 474571 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_530833 : Nat.Prime 530833 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_540901 : Nat.Prime 540901 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_559259 : Nat.Prime 559259 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_585911 : Nat.Prime 585911 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_588383 : Nat.Prime 588383 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_604277 : Nat.Prime 604277 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_636133 : Nat.Prime 636133 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_637841 : Nat.Prime 637841 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_640933 : Nat.Prime 640933 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_643961 : Nat.Prime 643961 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_648289 : Nat.Prime 648289 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_670811 : Nat.Prime 670811 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_699709 : Nat.Prime 699709 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_701609 : Nat.Prime 701609 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_717331 : Nat.Prime 717331 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_733813 : Nat.Prime 733813 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_752911 : Nat.Prime 752911 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_852671 : Nat.Prime 852671 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_862409 : Nat.Prime 862409 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_882253 : Nat.Prime 882253 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_886541 : Nat.Prime 886541 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_952583 : Nat.Prime 952583 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1012597 : Nat.Prime 1012597 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1040489 : Nat.Prime 1040489 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1068589 : Nat.Prime 1068589 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1152937 : Nat.Prime 1152937 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1154401 : Nat.Prime 1154401 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1168819 : Nat.Prime 1168819 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1233179 : Nat.Prime 1233179 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1245779 : Nat.Prime 1245779 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1287197 : Nat.Prime 1287197 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1300681 : Nat.Prime 1300681 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1335853 : Nat.Prime 1335853 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1379867 : Nat.Prime 1379867 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1430641 : Nat.Prime 1430641 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1442797 : Nat.Prime 1442797 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1455721 : Nat.Prime 1455721 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1525033 : Nat.Prime 1525033 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1602869 : Nat.Prime 1602869 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1743487 : Nat.Prime 1743487 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_1854943 : Nat.Prime 1854943 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2285333 : Nat.Prime 2285333 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2471461 : Nat.Prime 2471461 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2612719 : Nat.Prime 2612719 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2624581 : Nat.Prime 2624581 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2712719 : Nat.Prime 2712719 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2796397 : Nat.Prime 2796397 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2945309 : Nat.Prime 2945309 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_2991193 : Nat.Prime 2991193 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_3094661 : Nat.Prime 3094661 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_3192389 : Nat.Prime 3192389 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_3232393 : Nat.Prime 3232393 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_3367583 : Nat.Prime 3367583 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_3445999 : Nat.Prime 3445999 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_3553673 : Nat.Prime 3553673 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_3814501 : Nat.Prime 3814501 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4091299 : Nat.Prime 4091299 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4329937 : Nat.Prime 4329937 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4684117 : Nat.Prime 4684117 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4735909 : Nat.Prime 4735909 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_4764629 : Nat.Prime 4764629 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_5143253 : Nat.Prime 5143253 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_5424509 : Nat.Prime 5424509 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_5816549 : Nat.Prime 5816549 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_5828189 : Nat.Prime 5828189 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_5956133 : Nat.Prime 5956133 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_6336347 : Nat.Prime 6336347 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_6439561 : Nat.Prime 6439561 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_7181761 : Nat.Prime 7181761 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_7364299 : Nat.Prime 7364299 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_7444033 : Nat.Prime 7444033 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_7579493 : Nat.Prime 7579493 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_9281453 : Nat.Prime 9281453 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_10210243 : Nat.Prime 10210243 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_10390423 : Nat.Prime 10390423 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_10696681 : Nat.Prime 10696681 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_10820141 : Nat.Prime 10820141 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_10940987 : Nat.Prime 10940987 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_11791883 : Nat.Prime 11791883 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_11829439 : Nat.Prime 11829439 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_11958103 : Nat.Prime 11958103 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_12092323 : Nat.Prime 12092323 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_13245937 : Nat.Prime 13245937 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_13680577 : Nat.Prime 13680577 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_14141989 : Nat.Prime 14141989 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_14668343 : Nat.Prime 14668343 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_15549563 : Nat.Prime 15549563 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_15978517 : Nat.Prime 15978517 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_17833891 : Nat.Prime 17833891 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_19702603 : Nat.Prime 19702603 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_20054149 : Nat.Prime 20054149 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_21298187 : Nat.Prime 21298187 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_22155253 : Nat.Prime 22155253 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_22449137 : Nat.Prime 22449137 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_22949203 : Nat.Prime 22949203 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_23289997 : Nat.Prime 23289997 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_24187453 : Nat.Prime 24187453 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_24259177 : Nat.Prime 24259177 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_27085763 : Nat.Prime 27085763 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_28437443 : Nat.Prime 28437443 := by
  norm_num

private theorem prime_oneHundredSixtyTwoFD_31458437 : Nat.Prime 31458437 := by
  apply lucas_primality 31458437 (2 : ZMod 31458437)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (212557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (212557, 1)] : List FactorBlock).map factorBlockValue).prod) = 31458437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_37
      · exact prime_oneHundredSixtyTwoFD_212557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31458437) ^ 15729218 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 31458437) ^ 850228 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 31458437) ^ 148 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_32246411 : Nat.Prime 32246411 := by
  apply lucas_primality 32246411 (2 : ZMod 32246411)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (65809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (65809, 1)] : List FactorBlock).map factorBlockValue).prod) = 32246411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_65809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32246411) ^ 16123205 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 32246411) ^ 6449282 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 32246411) ^ 4606630 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 32246411) ^ 490 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_32934523 : Nat.Prime 32934523 := by
  apply lucas_primality 32934523 (3 : ZMod 32934523)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (227, 1), (24181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (227, 1), (24181, 1)] : List FactorBlock).map factorBlockValue).prod) = 32934523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_227
      · exact prime_oneHundredSixtyTwoFD_24181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 32934523) ^ 16467261 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 32934523) ^ 10978174 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 32934523) ^ 145086 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 32934523) ^ 1362 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_33677233 : Nat.Prime 33677233 := by
  apply lucas_primality 33677233 (5 : ZMod 33677233)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (701609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (701609, 1)] : List FactorBlock).map factorBlockValue).prod) = 33677233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_701609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 33677233) ^ 16838616 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 33677233) ^ 11225744 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 33677233) ^ 48 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_36225601 : Nat.Prime 36225601 := by
  apply lucas_primality 36225601 (7 : ZMod 36225601)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7547, 1)] : List FactorBlock).map factorBlockValue).prod) = 36225601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_7547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 36225601) ^ 18112800 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 36225601) ^ 12075200 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 36225601) ^ 7245120 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 36225601) ^ 4800 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_37097537 : Nat.Prime 37097537 := by
  apply lucas_primality 37097537 (3 : ZMod 37097537)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (17, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (17, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) = 37097537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_4871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37097537) ^ 18548768 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 5299648 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 2182208 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 7616 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_37312537 : Nat.Prime 37312537 := by
  apply lucas_primality 37312537 (5 : ZMod 37312537)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (311, 1), (4999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (311, 1), (4999, 1)] : List FactorBlock).map factorBlockValue).prod) = 37312537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_311
      · exact prime_oneHundredSixtyTwoFD_4999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 37312537) ^ 18656268 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 37312537) ^ 12437512 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 37312537) ^ 119976 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 37312537) ^ 7464 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_41385167 : Nat.Prime 41385167 := by
  apply lucas_primality 41385167 (5 : ZMod 41385167)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (559259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (559259, 1)] : List FactorBlock).map factorBlockValue).prod) = 41385167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_37
      · exact prime_oneHundredSixtyTwoFD_559259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 41385167) ^ 20692583 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 41385167) ^ 1118518 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 41385167) ^ 74 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_42135017 : Nat.Prime 42135017 := by
  apply lucas_primality 42135017 (3 : ZMod 42135017)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (73, 1), (937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (73, 1), (937, 1)] : List FactorBlock).map factorBlockValue).prod) = 42135017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_11
      · exact prime_oneHundredSixtyTwoFD_73
      · exact prime_oneHundredSixtyTwoFD_937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 42135017) ^ 21067508 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 42135017) ^ 6019288 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 42135017) ^ 3830456 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 42135017) ^ 577192 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 42135017) ^ 44968 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_44618071 : Nat.Prime 44618071 := by
  apply lucas_primality 44618071 (3 : ZMod 44618071)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (212467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (212467, 1)] : List FactorBlock).map factorBlockValue).prod) = 44618071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_212467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 44618071) ^ 22309035 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 44618071) ^ 14872690 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 44618071) ^ 8923614 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 44618071) ^ 6374010 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 44618071) ^ 210 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_45399371 : Nat.Prime 45399371 := by
  apply lucas_primality 45399371 (2 : ZMod 45399371)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (122701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (122701, 1)] : List FactorBlock).map factorBlockValue).prod) = 45399371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_37
      · exact prime_oneHundredSixtyTwoFD_122701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45399371) ^ 22699685 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 45399371) ^ 9079874 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 45399371) ^ 1227010 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 45399371) ^ 370 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_52474501 : Nat.Prime 52474501 := by
  apply lucas_primality 52474501 (14 : ZMod 52474501)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 3), (13, 2), (23, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 3), (13, 2), (23, 1)] : List FactorBlock).map factorBlockValue).prod) = 52474501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_23
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 52474501) ^ 26237250 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (14 : ZMod 52474501) ^ 17491500 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (14 : ZMod 52474501) ^ 10494900 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (14 : ZMod 52474501) ^ 4036500 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (14 : ZMod 52474501) ^ 2281500 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_1811
      · exact prime_oneHundredSixtyTwoFD_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_61405583 : Nat.Prime 61405583 := by
  apply lucas_primality 61405583 (5 : ZMod 61405583)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (149, 1), (29437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (149, 1), (29437, 1)] : List FactorBlock).map factorBlockValue).prod) = 61405583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_149
      · exact prime_oneHundredSixtyTwoFD_29437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 61405583) ^ 30702791 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 8772226 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 412118 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 2086 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_62021543 : Nat.Prime 62021543 := by
  apply lucas_primality 62021543 (5 : ZMod 62021543)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (165833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (165833, 1)] : List FactorBlock).map factorBlockValue).prod) = 62021543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_11
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_165833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 62021543) ^ 31010771 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 62021543) ^ 5638322 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 62021543) ^ 3648326 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 62021543) ^ 374 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_72248587 : Nat.Prime 72248587 := by
  apply lucas_primality 72248587 (2 : ZMod 72248587)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (139, 1), (86629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (139, 1), (86629, 1)] : List FactorBlock).map factorBlockValue).prod) = 72248587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_139
      · exact prime_oneHundredSixtyTwoFD_86629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 72248587) ^ 36124293 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 72248587) ^ 24082862 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 72248587) ^ 519774 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 72248587) ^ 834 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_82775113 : Nat.Prime 82775113 := by
  apply lucas_primality 82775113 (5 : ZMod 82775113)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (59, 1), (1193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (59, 1), (1193, 1)] : List FactorBlock).map factorBlockValue).prod) = 82775113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_59
      · exact prime_oneHundredSixtyTwoFD_1193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 82775113) ^ 41387556 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 82775113) ^ 27591704 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 82775113) ^ 11825016 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 82775113) ^ 1402968 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 82775113) ^ 69384 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_84395117 : Nat.Prime 84395117 := by
  apply lucas_primality 84395117 (2 : ZMod 84395117)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (439, 1), (3697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (439, 1), (3697, 1)] : List FactorBlock).map factorBlockValue).prod) = 84395117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_439
      · exact prime_oneHundredSixtyTwoFD_3697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 84395117) ^ 42197558 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 84395117) ^ 6491932 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 84395117) ^ 192244 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 84395117) ^ 22828 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_87527897 : Nat.Prime 87527897 := by
  apply lucas_primality 87527897 (3 : ZMod 87527897)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (10940987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (10940987, 1)] : List FactorBlock).map factorBlockValue).prod) = 87527897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_10940987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 87527897) ^ 43763948 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 87527897) ^ 8 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_89745571 : Nat.Prime 89745571 := by
  apply lucas_primality 89745571 (2 : ZMod 89745571)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (101, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (101, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) = 89745571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_101
      · exact prime_oneHundredSixtyTwoFD_1097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 89745571) ^ 44872785 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 89745571) ^ 29915190 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 89745571) ^ 17949114 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 89745571) ^ 888570 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 89745571) ^ 81810 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_90658541 : Nat.Prime 90658541 := by
  apply lucas_primality 90658541 (2 : ZMod 90658541)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (103, 1), (6287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (103, 1), (6287, 1)] : List FactorBlock).map factorBlockValue).prod) = 90658541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_103
      · exact prime_oneHundredSixtyTwoFD_6287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 90658541) ^ 45329270 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 90658541) ^ 18131708 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 90658541) ^ 12951220 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 90658541) ^ 880180 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 90658541) ^ 14420 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_96343309 : Nat.Prime 96343309 := by
  apply lucas_primality 96343309 (10 : ZMod 96343309)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (71, 1), (37693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (71, 1), (37693, 1)] : List FactorBlock).map factorBlockValue).prod) = 96343309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_71
      · exact prime_oneHundredSixtyTwoFD_37693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 96343309) ^ 48171654 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 96343309) ^ 32114436 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 96343309) ^ 1356948 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 96343309) ^ 2556 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_96570599 : Nat.Prime 96570599 := by
  apply lucas_primality 96570599 (11 : ZMod 96570599)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1951, 1), (24749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1951, 1), (24749, 1)] : List FactorBlock).map factorBlockValue).prod) = 96570599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_1951
      · exact prime_oneHundredSixtyTwoFD_24749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 96570599) ^ 48285299 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 96570599) ^ 49498 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 96570599) ^ 3902 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_100714093 : Nat.Prime 100714093 := by
  apply lucas_primality 100714093 (2 : ZMod 100714093)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1229, 1), (6829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1229, 1), (6829, 1)] : List FactorBlock).map factorBlockValue).prod) = 100714093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_1229
      · exact prime_oneHundredSixtyTwoFD_6829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 100714093) ^ 50357046 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 100714093) ^ 33571364 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 100714093) ^ 81948 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 100714093) ^ 14748 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_106008151 : Nat.Prime 106008151 := by
  apply lucas_primality 106008151 (3 : ZMod 106008151)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (23, 1), (30727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (23, 1), (30727, 1)] : List FactorBlock).map factorBlockValue).prod) = 106008151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_23
      · exact prime_oneHundredSixtyTwoFD_30727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 106008151) ^ 53004075 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 106008151) ^ 35336050 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 106008151) ^ 21201630 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 106008151) ^ 4609050 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 106008151) ^ 3450 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_109598317 : Nat.Prime 109598317 := by
  apply lucas_primality 109598317 (2 : ZMod 109598317)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1553, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1553, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod) = 109598317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_1553
      · exact prime_oneHundredSixtyTwoFD_5881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 109598317) ^ 54799158 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 109598317) ^ 36532772 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 109598317) ^ 70572 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 109598317) ^ 18636 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_117048473 : Nat.Prime 117048473 := by
  apply lucas_primality 117048473 (3 : ZMod 117048473)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (636133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (636133, 1)] : List FactorBlock).map factorBlockValue).prod) = 117048473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_23
      · exact prime_oneHundredSixtyTwoFD_636133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 117048473) ^ 58524236 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 117048473) ^ 5089064 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 117048473) ^ 184 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_118215619 : Nat.Prime 118215619 := by
  apply lucas_primality 118215619 (2 : ZMod 118215619)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19702603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19702603, 1)] : List FactorBlock).map factorBlockValue).prod) = 118215619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_19702603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 118215619) ^ 59107809 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 118215619) ^ 39405206 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 118215619) ^ 6 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_124058861 : Nat.Prime 124058861 := by
  apply lucas_primality 124058861 (2 : ZMod 124058861)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (364879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (364879, 1)] : List FactorBlock).map factorBlockValue).prod) = 124058861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_364879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 124058861) ^ 62029430 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 124058861) ^ 24811772 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 124058861) ^ 7297580 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 124058861) ^ 340 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_131433079 : Nat.Prime 131433079 := by
  apply lucas_primality 131433079 (17 : ZMod 131433079)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (223, 1), (14033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (223, 1), (14033, 1)] : List FactorBlock).map factorBlockValue).prod) = 131433079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_223
      · exact prime_oneHundredSixtyTwoFD_14033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 131433079) ^ 65716539 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 43811026 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 18776154 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 589386 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 9366 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_131747149 : Nat.Prime 131747149 := by
  apply lucas_primality 131747149 (10 : ZMod 131747149)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (13, 1), (31, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (13, 1), (31, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod) = 131747149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_31
      · exact prime_oneHundredSixtyTwoFD_1009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 131747149) ^ 65873574 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 131747149) ^ 43915716 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 131747149) ^ 10134396 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 131747149) ^ 4249908 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 131747149) ^ 130572 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_139568171 : Nat.Prime 139568171 := by
  apply lucas_primality 139568171 (2 : ZMod 139568171)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (284833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (284833, 1)] : List FactorBlock).map factorBlockValue).prod) = 139568171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_284833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 139568171) ^ 69784085 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 27913634 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 19938310 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 490 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_174243409 : Nat.Prime 174243409 := by
  apply lucas_primality 174243409 (11 : ZMod 174243409)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (73, 1), (49727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (73, 1), (49727, 1)] : List FactorBlock).map factorBlockValue).prod) = 174243409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_73
      · exact prime_oneHundredSixtyTwoFD_49727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 174243409) ^ 87121704 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 174243409) ^ 58081136 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 174243409) ^ 2386896 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 174243409) ^ 3504 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_189006211 : Nat.Prime 189006211 := by
  apply lucas_primality 189006211 (3 : ZMod 189006211)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (233341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (233341, 1)] : List FactorBlock).map factorBlockValue).prod) = 189006211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_233341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 189006211) ^ 94503105 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 189006211) ^ 63002070 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 189006211) ^ 37801242 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 189006211) ^ 810 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_202063399 : Nat.Prime 202063399 := by
  apply lucas_primality 202063399 (3 : ZMod 202063399)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (33677233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (33677233, 1)] : List FactorBlock).map factorBlockValue).prod) = 202063399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_33677233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 202063399) ^ 101031699 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 202063399) ^ 67354466 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 202063399) ^ 6 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_237905149 : Nat.Prime 237905149 := by
  apply lucas_primality 237905149 (7 : ZMod 237905149)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (1525033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (1525033, 1)] : List FactorBlock).map factorBlockValue).prod) = 237905149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_1525033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 237905149) ^ 118952574 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 237905149) ^ 79301716 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 237905149) ^ 18300396 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 237905149) ^ 156 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_263185981 : Nat.Prime 263185981 := by
  apply lucas_primality 263185981 (2 : ZMod 263185981)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1511, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1511, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod) = 263185981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_1511
      · exact prime_oneHundredSixtyTwoFD_2903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 263185981) ^ 131592990 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 263185981) ^ 87728660 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 263185981) ^ 52637196 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 263185981) ^ 174180 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 263185981) ^ 90660 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_289612139 : Nat.Prime 289612139 := by
  apply lucas_primality 289612139 (2 : ZMod 289612139)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (3367583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (3367583, 1)] : List FactorBlock).map factorBlockValue).prod) = 289612139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_43
      · exact prime_oneHundredSixtyTwoFD_3367583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 289612139) ^ 144806069 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 289612139) ^ 6735166 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 289612139) ^ 86 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_290249437 : Nat.Prime 290249437 := by
  apply lucas_primality 290249437 (5 : ZMod 290249437)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (24187453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (24187453, 1)] : List FactorBlock).map factorBlockValue).prod) = 290249437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_24187453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 290249437) ^ 145124718 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 290249437) ^ 96749812 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 290249437) ^ 12 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_314847007 : Nat.Prime 314847007 := by
  apply lucas_primality 314847007 (5 : ZMod 314847007)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (52474501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (52474501, 1)] : List FactorBlock).map factorBlockValue).prod) = 314847007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_52474501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 314847007) ^ 157423503 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 314847007) ^ 104949002 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 314847007) ^ 6 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_322725521 : Nat.Prime 322725521 := by
  apply lucas_primality 322725521 (3 : ZMod 322725521)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (13, 1), (310313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (13, 1), (310313, 1)] : List FactorBlock).map factorBlockValue).prod) = 322725521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_310313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 322725521) ^ 161362760 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 322725521) ^ 64545104 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 322725521) ^ 24825040 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 322725521) ^ 1040 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_379966547 : Nat.Prime 379966547 := by
  apply lucas_primality 379966547 (2 : ZMod 379966547)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7019, 1), (27067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7019, 1), (27067, 1)] : List FactorBlock).map factorBlockValue).prod) = 379966547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_7019
      · exact prime_oneHundredSixtyTwoFD_27067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 379966547) ^ 189983273 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 379966547) ^ 54134 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 379966547) ^ 14038 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_438393269 : Nat.Prime 438393269 := by
  apply lucas_primality 438393269 (2 : ZMod 438393269)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109598317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109598317, 1)] : List FactorBlock).map factorBlockValue).prod) = 438393269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_109598317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 438393269) ^ 219196634 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 438393269) ^ 4 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_457066601 : Nat.Prime 457066601 := by
  apply lucas_primality 457066601 (7 : ZMod 457066601)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (2285333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (2285333, 1)] : List FactorBlock).map factorBlockValue).prod) = 457066601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_2285333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 457066601) ^ 228533300 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 457066601) ^ 91413320 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 457066601) ^ 200 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_462521149 : Nat.Prime 462521149 := by
  apply lucas_primality 462521149 (2 : ZMod 462521149)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2549, 1), (15121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2549, 1), (15121, 1)] : List FactorBlock).map factorBlockValue).prod) = 462521149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_2549
      · exact prime_oneHundredSixtyTwoFD_15121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 462521149) ^ 231260574 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 462521149) ^ 154173716 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 462521149) ^ 181452 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 462521149) ^ 30588 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_494240567 : Nat.Prime 494240567 := by
  apply lucas_primality 494240567 (5 : ZMod 494240567)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (1381, 1), (1409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (1381, 1), (1409, 1)] : List FactorBlock).map factorBlockValue).prod) = 494240567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_127
      · exact prime_oneHundredSixtyTwoFD_1381
      · exact prime_oneHundredSixtyTwoFD_1409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 494240567) ^ 247120283 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 494240567) ^ 3891658 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 494240567) ^ 357886 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 494240567) ^ 350774 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_533050951 : Nat.Prime 533050951 := by
  apply lucas_primality 533050951 (12 : ZMod 533050951)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (3553673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (3553673, 1)] : List FactorBlock).map factorBlockValue).prod) = 533050951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_3553673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (12 : ZMod 533050951) ^ 266525475 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (12 : ZMod 533050951) ^ 177683650 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (12 : ZMod 533050951) ^ 106610190 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (12 : ZMod 533050951) ^ 150 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_540182551 : Nat.Prime 540182551 := by
  apply lucas_primality 540182551 (17 : ZMod 540182551)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (1049, 1), (3433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (1049, 1), (3433, 1)] : List FactorBlock).map factorBlockValue).prod) = 540182551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_1049
      · exact prime_oneHundredSixtyTwoFD_3433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 540182551) ^ 270091275 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 540182551) ^ 180060850 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 540182551) ^ 108036510 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 540182551) ^ 514950 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 540182551) ^ 157350 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_606112099 : Nat.Prime 606112099 := by
  apply lucas_primality 606112099 (2 : ZMod 606112099)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (631, 1), (160093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (631, 1), (160093, 1)] : List FactorBlock).map factorBlockValue).prod) = 606112099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_631
      · exact prime_oneHundredSixtyTwoFD_160093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 606112099) ^ 303056049 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 606112099) ^ 202037366 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 606112099) ^ 960558 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 606112099) ^ 3786 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_614504323 : Nat.Prime 614504323 := by
  apply lucas_primality 614504323 (2 : ZMod 614504323)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4733, 1), (7213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4733, 1), (7213, 1)] : List FactorBlock).map factorBlockValue).prod) = 614504323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_4733
      · exact prime_oneHundredSixtyTwoFD_7213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 614504323) ^ 307252161 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 614504323) ^ 204834774 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 614504323) ^ 129834 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 614504323) ^ 85194 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_11
      · exact prime_oneHundredSixtyTwoFD_19
      · exact prime_oneHundredSixtyTwoFD_61
      · exact prime_oneHundredSixtyTwoFD_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_679623851 : Nat.Prime 679623851 := by
  apply lucas_primality 679623851 (2 : ZMod 679623851)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (31, 1), (438467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (31, 1), (438467, 1)] : List FactorBlock).map factorBlockValue).prod) = 679623851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_31
      · exact prime_oneHundredSixtyTwoFD_438467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 679623851) ^ 339811925 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 679623851) ^ 135924770 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 679623851) ^ 21923350 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 679623851) ^ 1550 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_704229839 : Nat.Prime 704229839 := by
  apply lucas_primality 704229839 (11 : ZMod 704229839)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (27085763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (27085763, 1)] : List FactorBlock).map factorBlockValue).prod) = 704229839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_27085763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 704229839) ^ 352114919 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 704229839) ^ 54171526 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 704229839) ^ 26 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_705036473 : Nat.Prime 705036473 := by
  apply lucas_primality 705036473 (3 : ZMod 705036473)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (31, 1), (47, 1), (8641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (31, 1), (47, 1), (8641, 1)] : List FactorBlock).map factorBlockValue).prod) = 705036473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_31
      · exact prime_oneHundredSixtyTwoFD_47
      · exact prime_oneHundredSixtyTwoFD_8641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 705036473) ^ 352518236 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 705036473) ^ 100719496 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 705036473) ^ 22743112 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 705036473) ^ 15000776 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 705036473) ^ 81592 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_705434131 : Nat.Prime 705434131 := by
  apply lucas_primality 705434131 (10 : ZMod 705434131)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (2612719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (2612719, 1)] : List FactorBlock).map factorBlockValue).prod) = 705434131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_2612719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 705434131) ^ 352717065 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 705434131) ^ 235144710 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 705434131) ^ 141086826 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 705434131) ^ 270 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_17203
      · exact prime_oneHundredSixtyTwoFD_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_754827223 : Nat.Prime 754827223 := by
  apply lucas_primality 754827223 (3 : ZMod 754827223)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (283, 1), (444539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (283, 1), (444539, 1)] : List FactorBlock).map factorBlockValue).prod) = 754827223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_283
      · exact prime_oneHundredSixtyTwoFD_444539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 754827223) ^ 377413611 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 754827223) ^ 251609074 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 754827223) ^ 2667234 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 754827223) ^ 1698 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_792690473 : Nat.Prime 792690473 := by
  apply lucas_primality 792690473 (3 : ZMod 792690473)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (53, 1), (103, 1), (2593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (53, 1), (103, 1), (2593, 1)] : List FactorBlock).map factorBlockValue).prod) = 792690473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_53
      · exact prime_oneHundredSixtyTwoFD_103
      · exact prime_oneHundredSixtyTwoFD_2593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 792690473) ^ 396345236 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 792690473) ^ 113241496 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 792690473) ^ 14956424 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 792690473) ^ 7696024 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 792690473) ^ 305704 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_906208483 : Nat.Prime 906208483 := by
  apply lucas_primality 906208483 (2 : ZMod 906208483)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (131, 1), (1152937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (131, 1), (1152937, 1)] : List FactorBlock).map factorBlockValue).prod) = 906208483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_131
      · exact prime_oneHundredSixtyTwoFD_1152937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 906208483) ^ 453104241 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 302069494 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 6917622 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 786 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_963433091 : Nat.Prime 963433091 := by
  apply lucas_primality 963433091 (2 : ZMod 963433091)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (96343309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (96343309, 1)] : List FactorBlock).map factorBlockValue).prod) = 963433091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_96343309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 963433091) ^ 481716545 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 963433091) ^ 192686618 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 963433091) ^ 10 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_971025637 : Nat.Prime 971025637 := by
  apply lucas_primality 971025637 (2 : ZMod 971025637)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (233, 1), (49613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (233, 1), (49613, 1)] : List FactorBlock).map factorBlockValue).prod) = 971025637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_233
      · exact prime_oneHundredSixtyTwoFD_49613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 971025637) ^ 485512818 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 971025637) ^ 323675212 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 971025637) ^ 138717948 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 971025637) ^ 4167492 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 971025637) ^ 19572 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1019141639 : Nat.Prime 1019141639 := by
  apply lucas_primality 1019141639 (17 : ZMod 1019141639)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (22155253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (22155253, 1)] : List FactorBlock).map factorBlockValue).prod) = 1019141639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_23
      · exact prime_oneHundredSixtyTwoFD_22155253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 1019141639) ^ 509570819 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 1019141639) ^ 44310506 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 1019141639) ^ 46 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1053156017 : Nat.Prime 1053156017 := by
  apply lucas_primality 1053156017 (3 : ZMod 1053156017)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (19, 1), (23, 1), (13693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (19, 1), (23, 1), (13693, 1)] : List FactorBlock).map factorBlockValue).prod) = 1053156017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_11
      · exact prime_oneHundredSixtyTwoFD_19
      · exact prime_oneHundredSixtyTwoFD_23
      · exact prime_oneHundredSixtyTwoFD_13693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1053156017) ^ 526578008 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1053156017) ^ 95741456 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1053156017) ^ 55429264 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1053156017) ^ 45789392 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1053156017) ^ 76912 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1155977393 : Nat.Prime 1155977393 := by
  apply lucas_primality 1155977393 (3 : ZMod 1155977393)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (72248587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (72248587, 1)] : List FactorBlock).map factorBlockValue).prod) = 1155977393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_72248587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1155977393) ^ 577988696 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1155977393) ^ 16 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1194372607 : Nat.Prime 1194372607 := by
  apply lucas_primality 1194372607 (3 : ZMod 1194372607)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (28437443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (28437443, 1)] : List FactorBlock).map factorBlockValue).prod) = 1194372607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_28437443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1194372607) ^ 597186303 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1194372607) ^ 398124202 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1194372607) ^ 170624658 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1194372607) ^ 42 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1800601883 : Nat.Prime 1800601883 := by
  apply lucas_primality 1800601883 (2 : ZMod 1800601883)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (9281453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (9281453, 1)] : List FactorBlock).map factorBlockValue).prod) = 1800601883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_97
      · exact prime_oneHundredSixtyTwoFD_9281453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1800601883) ^ 900300941 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1800601883) ^ 18562906 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1800601883) ^ 194 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1889082043 : Nat.Prime 1889082043 := by
  apply lucas_primality 1889082043 (2 : ZMod 1889082043)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (314847007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (314847007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1889082043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_314847007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1889082043) ^ 944541021 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1889082043) ^ 629694014 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1889082043) ^ 6 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1931411981 : Nat.Prime 1931411981 := by
  apply lucas_primality 1931411981 (2 : ZMod 1931411981)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (96570599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (96570599, 1)] : List FactorBlock).map factorBlockValue).prod) = 1931411981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_96570599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1931411981) ^ 965705990 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1931411981) ^ 386282396 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1931411981) ^ 20 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_2038283279 : Nat.Prime 2038283279 := by
  apply lucas_primality 2038283279 (7 : ZMod 2038283279)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1019141639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1019141639, 1)] : List FactorBlock).map factorBlockValue).prod) = 2038283279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_1019141639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 2038283279) ^ 1019141639 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 2038283279) ^ 2 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_2311954787 : Nat.Prime 2311954787 := by
  apply lucas_primality 2311954787 (2 : ZMod 2311954787)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1155977393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1155977393, 1)] : List FactorBlock).map factorBlockValue).prod) = 2311954787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_1155977393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2311954787) ^ 1155977393 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2311954787) ^ 2 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_2654369689 : Nat.Prime 2654369689 := by
  apply lucas_primality 2654369689 (7 : ZMod 2654369689)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (101, 1), (719, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (101, 1), (719, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) = 2654369689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_101
      · exact prime_oneHundredSixtyTwoFD_719
      · exact prime_oneHundredSixtyTwoFD_1523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2654369689) ^ 1327184844 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 2654369689) ^ 884789896 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 2654369689) ^ 26280888 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 2654369689) ^ 3691752 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 2654369689) ^ 1742856 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_2806907717 : Nat.Prime 2806907717 := by
  apply lucas_primality 2806907717 (2 : ZMod 2806907717)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (21683, 1), (32363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (21683, 1), (32363, 1)] : List FactorBlock).map factorBlockValue).prod) = 2806907717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_21683
      · exact prime_oneHundredSixtyTwoFD_32363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2806907717) ^ 1403453858 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2806907717) ^ 129452 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2806907717) ^ 86732 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_3163746367 : Nat.Prime 3163746367 := by
  apply lucas_primality 3163746367 (3 : ZMod 3163746367)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (15978517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (15978517, 1)] : List FactorBlock).map factorBlockValue).prod) = 3163746367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_11
      · exact prime_oneHundredSixtyTwoFD_15978517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3163746367) ^ 1581873183 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3163746367) ^ 1054582122 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3163746367) ^ 287613306 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3163746367) ^ 198 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_3446621173 : Nat.Prime 3446621173 := by
  apply lucas_primality 3446621173 (5 : ZMod 3446621173)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (59, 1), (540901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (59, 1), (540901, 1)] : List FactorBlock).map factorBlockValue).prod) = 3446621173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_59
      · exact prime_oneHundredSixtyTwoFD_540901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3446621173) ^ 1723310586 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3446621173) ^ 1148873724 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3446621173) ^ 58417308 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3446621173) ^ 6372 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_3758823767 : Nat.Prime 3758823767 := by
  apply lucas_primality 3758823767 (5 : ZMod 3758823767)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (967, 1), (1217, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (967, 1), (1217, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) = 3758823767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_967
      · exact prime_oneHundredSixtyTwoFD_1217
      · exact prime_oneHundredSixtyTwoFD_1597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3758823767) ^ 1879411883 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3758823767) ^ 3887098 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3758823767) ^ 3088598 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3758823767) ^ 2353678 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_4092387857 : Nat.Prime 4092387857 := by
  apply lucas_primality 4092387857 (3 : ZMod 4092387857)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (401, 1), (637841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (401, 1), (637841, 1)] : List FactorBlock).map factorBlockValue).prod) = 4092387857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_401
      · exact prime_oneHundredSixtyTwoFD_637841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4092387857) ^ 2046193928 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4092387857) ^ 10205456 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4092387857) ^ 6416 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_4094244251 : Nat.Prime 4094244251 := by
  apply lucas_primality 4094244251 (10 : ZMod 4094244251)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (37, 1), (113, 1), (3917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (37, 1), (113, 1), (3917, 1)] : List FactorBlock).map factorBlockValue).prod) = 4094244251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_37
      · exact prime_oneHundredSixtyTwoFD_113
      · exact prime_oneHundredSixtyTwoFD_3917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 4094244251) ^ 2047122125 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 4094244251) ^ 818848850 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 4094244251) ^ 110655250 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 4094244251) ^ 36232250 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 4094244251) ^ 1045250 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_5734224997 : Nat.Prime 5734224997 := by
  apply lucas_primality 5734224997 (2 : ZMod 5734224997)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1609, 1), (296987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1609, 1), (296987, 1)] : List FactorBlock).map factorBlockValue).prod) = 5734224997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_1609
      · exact prime_oneHundredSixtyTwoFD_296987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5734224997) ^ 2867112498 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5734224997) ^ 1911408332 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5734224997) ^ 3563844 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5734224997) ^ 19308 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_5746793477 : Nat.Prime 5746793477 := by
  apply lucas_primality 5746793477 (2 : ZMod 5746793477)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (193, 1), (7444033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (193, 1), (7444033, 1)] : List FactorBlock).map factorBlockValue).prod) = 5746793477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_193
      · exact prime_oneHundredSixtyTwoFD_7444033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5746793477) ^ 2873396738 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5746793477) ^ 29776132 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5746793477) ^ 772 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_31
      · exact prime_oneHundredSixtyTwoFD_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_7556328173 : Nat.Prime 7556328173 := by
  apply lucas_primality 7556328173 (2 : ZMod 7556328173)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1889082043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1889082043, 1)] : List FactorBlock).map factorBlockValue).prod) = 7556328173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_1889082043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7556328173) ^ 3778164086 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7556328173) ^ 4 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_7598863621 : Nat.Prime 7598863621 := by
  apply lucas_primality 7598863621 (2 : ZMod 7598863621)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (29, 1), (1455721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (29, 1), (1455721, 1)] : List FactorBlock).map factorBlockValue).prod) = 7598863621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_29
      · exact prime_oneHundredSixtyTwoFD_1455721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7598863621) ^ 3799431810 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7598863621) ^ 2532954540 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7598863621) ^ 1519772724 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7598863621) ^ 262029780 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7598863621) ^ 5220 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_8732808121 : Nat.Prime 8732808121 := by
  apply lucas_primality 8732808121 (13 : ZMod 8732808121)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (19, 1), (41, 1), (93419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (19, 1), (41, 1), (93419, 1)] : List FactorBlock).map factorBlockValue).prod) = 8732808121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_19
      · exact prime_oneHundredSixtyTwoFD_41
      · exact prime_oneHundredSixtyTwoFD_93419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 8732808121) ^ 4366404060 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (13 : ZMod 8732808121) ^ 2910936040 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (13 : ZMod 8732808121) ^ 1746561624 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (13 : ZMod 8732808121) ^ 459621480 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (13 : ZMod 8732808121) ^ 212995320 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (13 : ZMod 8732808121) ^ 93480 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_10284917603 : Nat.Prime 10284917603 := by
  apply lucas_primality 10284917603 (2 : ZMod 10284917603)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (163, 1), (852671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (163, 1), (852671, 1)] : List FactorBlock).map factorBlockValue).prod) = 10284917603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_37
      · exact prime_oneHundredSixtyTwoFD_163
      · exact prime_oneHundredSixtyTwoFD_852671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10284917603) ^ 5142458801 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10284917603) ^ 277970746 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10284917603) ^ 63097654 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10284917603) ^ 12062 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_10803266219 : Nat.Prime 10803266219 := by
  apply lucas_primality 10803266219 (2 : ZMod 10803266219)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (131747149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (131747149, 1)] : List FactorBlock).map factorBlockValue).prod) = 10803266219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_41
      · exact prime_oneHundredSixtyTwoFD_131747149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10803266219) ^ 5401633109 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10803266219) ^ 263494298 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10803266219) ^ 82 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_11388258337 : Nat.Prime 11388258337 := by
  apply lucas_primality 11388258337 (10 : ZMod 11388258337)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (13, 2), (149, 1), (673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (13, 2), (149, 1), (673, 1)] : List FactorBlock).map factorBlockValue).prod) = 11388258337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_149
      · exact prime_oneHundredSixtyTwoFD_673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 11388258337) ^ 5694129168 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 11388258337) ^ 3796086112 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 11388258337) ^ 1626894048 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 11388258337) ^ 876019872 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 11388258337) ^ 76431264 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 11388258337) ^ 16921632 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_16287860131 : Nat.Prime 16287860131 := by
  apply lucas_primality 16287860131 (10 : ZMod 16287860131)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (67, 1), (137, 1), (59149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (67, 1), (137, 1), (59149, 1)] : List FactorBlock).map factorBlockValue).prod) = 16287860131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_67
      · exact prime_oneHundredSixtyTwoFD_137
      · exact prime_oneHundredSixtyTwoFD_59149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 16287860131) ^ 8143930065 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 16287860131) ^ 5429286710 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 16287860131) ^ 3257572026 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 16287860131) ^ 243102390 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 16287860131) ^ 118889490 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 16287860131) ^ 275370 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_16544752451 : Nat.Prime 16544752451 := by
  apply lucas_primality 16544752451 (6 : ZMod 16544752451)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (61, 1), (5424509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (61, 1), (5424509, 1)] : List FactorBlock).map factorBlockValue).prod) = 16544752451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_61
      · exact prime_oneHundredSixtyTwoFD_5424509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 16544752451) ^ 8272376225 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 16544752451) ^ 3308950490 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 16544752451) ^ 271225450 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 16544752451) ^ 3050 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_17511197201 : Nat.Prime 17511197201 := by
  apply lucas_primality 17511197201 (3 : ZMod 17511197201)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (7, 1), (23, 1), (37, 1), (7349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (7, 1), (23, 1), (37, 1), (7349, 1)] : List FactorBlock).map factorBlockValue).prod) = 17511197201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_23
      · exact prime_oneHundredSixtyTwoFD_37
      · exact prime_oneHundredSixtyTwoFD_7349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17511197201) ^ 8755598600 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 17511197201) ^ 3502239440 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 17511197201) ^ 2501599600 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 17511197201) ^ 761356400 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 17511197201) ^ 473275600 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 17511197201) ^ 2382800 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_18519708707 : Nat.Prime 18519708707 := by
  apply lucas_primality 18519708707 (2 : ZMod 18519708707)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (1033, 1), (70583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (1033, 1), (70583, 1)] : List FactorBlock).map factorBlockValue).prod) = 18519708707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_127
      · exact prime_oneHundredSixtyTwoFD_1033
      · exact prime_oneHundredSixtyTwoFD_70583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18519708707) ^ 9259854353 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18519708707) ^ 145824478 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18519708707) ^ 17928082 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18519708707) ^ 262382 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_20569835207 : Nat.Prime 20569835207 := by
  apply lucas_primality 20569835207 (5 : ZMod 20569835207)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10284917603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10284917603, 1)] : List FactorBlock).map factorBlockValue).prod) = 20569835207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_10284917603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 20569835207) ^ 10284917603 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 20569835207) ^ 2 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_21581357527 : Nat.Prime 21581357527 := by
  apply lucas_primality 21581357527 (5 : ZMod 21581357527)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (277, 1), (1442797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (277, 1), (1442797, 1)] : List FactorBlock).map factorBlockValue).prod) = 21581357527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_277
      · exact prime_oneHundredSixtyTwoFD_1442797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 21581357527) ^ 10790678763 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 21581357527) ^ 7193785842 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 21581357527) ^ 77911038 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 21581357527) ^ 14958 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_22936899989 : Nat.Prime 22936899989 := by
  apply lucas_primality 22936899989 (2 : ZMod 22936899989)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5734224997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5734224997, 1)] : List FactorBlock).map factorBlockValue).prod) = 22936899989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5734224997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 22936899989) ^ 11468449994 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 22936899989) ^ 4 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_23046330287 : Nat.Prime 23046330287 := by
  apply lucas_primality 23046330287 (7 : ZMod 23046330287)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (173, 1), (1583, 1), (6011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (173, 1), (1583, 1), (6011, 1)] : List FactorBlock).map factorBlockValue).prod) = 23046330287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_173
      · exact prime_oneHundredSixtyTwoFD_1583
      · exact prime_oneHundredSixtyTwoFD_6011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 23046330287) ^ 11523165143 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 3292332898 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 133215782 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 14558642 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 3834026 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_25790344861 : Nat.Prime 25790344861 := by
  apply lucas_primality 25790344861 (2 : ZMod 25790344861)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (61405583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (61405583, 1)] : List FactorBlock).map factorBlockValue).prod) = 25790344861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_61405583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25790344861) ^ 12895172430 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 8596781620 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 5158068972 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 3684334980 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 420 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_26772858811 : Nat.Prime 26772858811 := by
  apply lucas_primality 26772858811 (17 : ZMod 26772858811)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (101, 1), (2945309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (101, 1), (2945309, 1)] : List FactorBlock).map factorBlockValue).prod) = 26772858811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_101
      · exact prime_oneHundredSixtyTwoFD_2945309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 26772858811) ^ 13386429405 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 26772858811) ^ 8924286270 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 26772858811) ^ 5354571762 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 26772858811) ^ 265077810 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 26772858811) ^ 9090 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_28928527039 : Nat.Prime 28928527039 := by
  apply lucas_primality 28928527039 (3 : ZMod 28928527039)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (157, 1), (163, 1), (62801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (157, 1), (163, 1), (62801, 1)] : List FactorBlock).map factorBlockValue).prod) = 28928527039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_157
      · exact prime_oneHundredSixtyTwoFD_163
      · exact prime_oneHundredSixtyTwoFD_62801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 28928527039) ^ 14464263519 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 28928527039) ^ 9642842346 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 28928527039) ^ 184258134 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 28928527039) ^ 177475626 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 28928527039) ^ 460638 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_29553664193 : Nat.Prime 29553664193 := by
  apply lucas_primality 29553664193 (3 : ZMod 29553664193)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (13, 1), (241, 1), (147391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (13, 1), (241, 1), (147391, 1)] : List FactorBlock).map factorBlockValue).prod) = 29553664193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_241
      · exact prime_oneHundredSixtyTwoFD_147391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 29553664193) ^ 14776832096 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 29553664193) ^ 2273358784 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 29553664193) ^ 122629312 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 29553664193) ^ 200512 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_29606367953 : Nat.Prime 29606367953 := by
  apply lucas_primality 29606367953 (3 : ZMod 29606367953)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (17, 1), (15549563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (17, 1), (15549563, 1)] : List FactorBlock).map factorBlockValue).prod) = 29606367953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_15549563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 29606367953) ^ 14803183976 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 29606367953) ^ 4229481136 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 29606367953) ^ 1741551056 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 29606367953) ^ 1904 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_31009114457 : Nat.Prime 31009114457 := by
  apply lucas_primality 31009114457 (3 : ZMod 31009114457)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (107, 1), (36225601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (107, 1), (36225601, 1)] : List FactorBlock).map factorBlockValue).prod) = 31009114457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_107
      · exact prime_oneHundredSixtyTwoFD_36225601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 31009114457) ^ 15504557228 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 31009114457) ^ 289804808 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 31009114457) ^ 856 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_36592649867 : Nat.Prime 36592649867 := by
  apply lucas_primality 36592649867 (2 : ZMod 36592649867)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (3637, 1), (82469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (3637, 1), (82469, 1)] : List FactorBlock).map factorBlockValue).prod) = 36592649867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_61
      · exact prime_oneHundredSixtyTwoFD_3637
      · exact prime_oneHundredSixtyTwoFD_82469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36592649867) ^ 18296324933 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 36592649867) ^ 599879506 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 36592649867) ^ 10061218 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 36592649867) ^ 443714 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_61805183393 : Nat.Prime 61805183393 := by
  apply lucas_primality 61805183393 (3 : ZMod 61805183393)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (1931411981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (1931411981, 1)] : List FactorBlock).map factorBlockValue).prod) = 61805183393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_1931411981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 61805183393) ^ 30902591696 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 61805183393) ^ 32 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_76552219141 : Nat.Prime 76552219141 := by
  apply lucas_primality 76552219141 (2 : ZMod 76552219141)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (47, 1), (313, 1), (86729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (47, 1), (313, 1), (86729, 1)] : List FactorBlock).map factorBlockValue).prod) = 76552219141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_47
      · exact prime_oneHundredSixtyTwoFD_313
      · exact prime_oneHundredSixtyTwoFD_86729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 76552219141) ^ 38276109570 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 76552219141) ^ 25517406380 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 76552219141) ^ 15310443828 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 76552219141) ^ 1628770620 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 76552219141) ^ 244575780 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 76552219141) ^ 882660 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_85204051633 : Nat.Prime 85204051633 := by
  apply lucas_primality 85204051633 (10 : ZMod 85204051633)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (7, 1), (23, 1), (408347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (7, 1), (23, 1), (408347, 1)] : List FactorBlock).map factorBlockValue).prod) = 85204051633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_23
      · exact prime_oneHundredSixtyTwoFD_408347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 85204051633) ^ 42602025816 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 85204051633) ^ 28401350544 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 85204051633) ^ 12172007376 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 85204051633) ^ 3704523984 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 85204051633) ^ 208656 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_89706362731 : Nat.Prime 89706362731 := by
  apply lucas_primality 89706362731 (2 : ZMod 89706362731)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (499, 1), (161957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (499, 1), (161957, 1)] : List FactorBlock).map factorBlockValue).prod) = 89706362731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_37
      · exact prime_oneHundredSixtyTwoFD_499
      · exact prime_oneHundredSixtyTwoFD_161957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 89706362731) ^ 44853181365 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 89706362731) ^ 29902120910 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 89706362731) ^ 17941272546 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 89706362731) ^ 2424496290 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 89706362731) ^ 179772270 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 89706362731) ^ 553890 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_118138253869 : Nat.Prime 118138253869 := by
  apply lucas_primality 118138253869 (2 : ZMod 118138253869)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (29, 2), (1300681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (29, 2), (1300681, 1)] : List FactorBlock).map factorBlockValue).prod) = 118138253869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_29
      · exact prime_oneHundredSixtyTwoFD_1300681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 118138253869) ^ 59069126934 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 118138253869) ^ 39379417956 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 118138253869) ^ 4073732892 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 118138253869) ^ 90828 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_137018091817 : Nat.Prime 137018091817 := by
  apply lucas_primality 137018091817 (7 : ZMod 137018091817)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (4799, 1), (396547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (4799, 1), (396547, 1)] : List FactorBlock).map factorBlockValue).prod) = 137018091817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_4799
      · exact prime_oneHundredSixtyTwoFD_396547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 137018091817) ^ 68509045908 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 137018091817) ^ 45672697272 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 137018091817) ^ 28551384 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 137018091817) ^ 345528 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_148945151149 : Nat.Prime 148945151149 := by
  apply lucas_primality 148945151149 (2 : ZMod 148945151149)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (223, 1), (1069, 1), (52067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (223, 1), (1069, 1), (52067, 1)] : List FactorBlock).map factorBlockValue).prod) = 148945151149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_223
      · exact prime_oneHundredSixtyTwoFD_1069
      · exact prime_oneHundredSixtyTwoFD_52067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 148945151149) ^ 74472575574 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 148945151149) ^ 49648383716 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 148945151149) ^ 667915476 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 148945151149) ^ 139331292 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 148945151149) ^ 2860644 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_157705373099 : Nat.Prime 157705373099 := by
  apply lucas_primality 157705373099 (2 : ZMod 157705373099)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (13, 1), (71, 1), (1743487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (13, 1), (71, 1), (1743487, 1)] : List FactorBlock).map factorBlockValue).prod) = 157705373099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_71
      · exact prime_oneHundredSixtyTwoFD_1743487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 157705373099) ^ 78852686549 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 157705373099) ^ 22529339014 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 157705373099) ^ 12131182546 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 157705373099) ^ 2221202438 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 157705373099) ^ 90454 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_164171600897 : Nat.Prime 164171600897 := by
  apply lucas_primality 164171600897 (3 : ZMod 164171600897)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (239, 1), (670811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (239, 1), (670811, 1)] : List FactorBlock).map factorBlockValue).prod) = 164171600897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_239
      · exact prime_oneHundredSixtyTwoFD_670811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 164171600897) ^ 82085800448 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 164171600897) ^ 686910464 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 164171600897) ^ 244736 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_177602339353 : Nat.Prime 177602339353 := by
  apply lucas_primality 177602339353 (5 : ZMod 177602339353)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (163, 1), (45399371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (163, 1), (45399371, 1)] : List FactorBlock).map factorBlockValue).prod) = 177602339353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_163
      · exact prime_oneHundredSixtyTwoFD_45399371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 177602339353) ^ 88801169676 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 177602339353) ^ 59200779784 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 177602339353) ^ 1089584904 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 177602339353) ^ 3912 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_194322970511 : Nat.Prime 194322970511 := by
  apply lucas_primality 194322970511 (13 : ZMod 194322970511)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (127, 1), (2879, 1), (53147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (127, 1), (2879, 1), (53147, 1)] : List FactorBlock).map factorBlockValue).prod) = 194322970511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_127
      · exact prime_oneHundredSixtyTwoFD_2879
      · exact prime_oneHundredSixtyTwoFD_53147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 194322970511) ^ 97161485255 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (13 : ZMod 194322970511) ^ 38864594102 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (13 : ZMod 194322970511) ^ 1530102130 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (13 : ZMod 194322970511) ^ 67496690 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (13 : ZMod 194322970511) ^ 3656330 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_205388449943 : Nat.Prime 205388449943 := by
  apply lucas_primality 205388449943 (5 : ZMod 205388449943)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 2), (19, 1), (137, 1), (10501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 2), (19, 1), (137, 1), (10501, 1)] : List FactorBlock).map factorBlockValue).prod) = 205388449943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_19
      · exact prime_oneHundredSixtyTwoFD_137
      · exact prime_oneHundredSixtyTwoFD_10501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 205388449943) ^ 102694224971 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 205388449943) ^ 15799111534 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 205388449943) ^ 12081673526 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 205388449943) ^ 10809918418 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 205388449943) ^ 1499185766 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 205388449943) ^ 19558942 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_210220280311 : Nat.Prime 210220280311 := by
  apply lucas_primality 210220280311 (12 : ZMod 210220280311)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (41, 1), (227, 1), (752911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (41, 1), (227, 1), (752911, 1)] : List FactorBlock).map factorBlockValue).prod) = 210220280311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_41
      · exact prime_oneHundredSixtyTwoFD_227
      · exact prime_oneHundredSixtyTwoFD_752911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 210220280311) ^ 105110140155 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (12 : ZMod 210220280311) ^ 70073426770 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (12 : ZMod 210220280311) ^ 42044056062 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (12 : ZMod 210220280311) ^ 5127323910 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (12 : ZMod 210220280311) ^ 926080530 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (12 : ZMod 210220280311) ^ 279210 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_238024728587 : Nat.Prime 238024728587 := by
  apply lucas_primality 238024728587 (5 : ZMod 238024728587)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (71, 1), (137, 1), (643961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (71, 1), (137, 1), (643961, 1)] : List FactorBlock).map factorBlockValue).prod) = 238024728587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_19
      · exact prime_oneHundredSixtyTwoFD_71
      · exact prime_oneHundredSixtyTwoFD_137
      · exact prime_oneHundredSixtyTwoFD_643961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 238024728587) ^ 119012364293 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 238024728587) ^ 12527617294 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 238024728587) ^ 3352460966 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 238024728587) ^ 1737406778 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 238024728587) ^ 369626 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_19
      · exact prime_oneHundredSixtyTwoFD_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_272316954397 : Nat.Prime 272316954397 := by
  apply lucas_primality 272316954397 (5 : ZMod 272316954397)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (1194372607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (1194372607, 1)] : List FactorBlock).map factorBlockValue).prod) = 272316954397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_19
      · exact prime_oneHundredSixtyTwoFD_1194372607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 272316954397) ^ 136158477198 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 272316954397) ^ 90772318132 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 272316954397) ^ 14332471284 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 272316954397) ^ 228 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_410776899887 : Nat.Prime 410776899887 := by
  apply lucas_primality 410776899887 (5 : ZMod 410776899887)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (205388449943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (205388449943, 1)] : List FactorBlock).map factorBlockValue).prod) = 410776899887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_205388449943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 410776899887) ^ 205388449943 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 410776899887) ^ 2 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_413751298703 : Nat.Prime 413751298703 := by
  apply lucas_primality 413751298703 (5 : ZMod 413751298703)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29553664193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29553664193, 1)] : List FactorBlock).map factorBlockValue).prod) = 413751298703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_29553664193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 413751298703) ^ 206875649351 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 413751298703) ^ 59107328386 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 413751298703) ^ 14 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_551692173793 : Nat.Prime 551692173793 := by
  apply lucas_primality 551692173793 (7 : ZMod 551692173793)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5746793477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5746793477, 1)] : List FactorBlock).map factorBlockValue).prod) = 551692173793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5746793477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 551692173793) ^ 275846086896 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 551692173793) ^ 183897391264 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 551692173793) ^ 96 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_605134725067 : Nat.Prime 605134725067 := by
  apply lucas_primality 605134725067 (2 : ZMod 605134725067)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (53, 1), (37312537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (53, 1), (37312537, 1)] : List FactorBlock).map factorBlockValue).prod) = 605134725067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_53
      · exact prime_oneHundredSixtyTwoFD_37312537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 605134725067) ^ 302567362533 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 605134725067) ^ 201711575022 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 605134725067) ^ 35596160298 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 605134725067) ^ 11417636322 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 605134725067) ^ 16218 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_623106816923 : Nat.Prime 623106816923 := by
  apply lucas_primality 623106816923 (2 : ZMod 623106816923)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (7598863621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (7598863621, 1)] : List FactorBlock).map factorBlockValue).prod) = 623106816923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_41
      · exact prime_oneHundredSixtyTwoFD_7598863621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 623106816923) ^ 311553408461 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 623106816923) ^ 15197727242 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 623106816923) ^ 82 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_733766155919 : Nat.Prime 733766155919 := by
  apply lucas_primality 733766155919 (11 : ZMod 733766155919)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (21581357527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (21581357527, 1)] : List FactorBlock).map factorBlockValue).prod) = 733766155919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_21581357527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 733766155919) ^ 366883077959 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 733766155919) ^ 43162715054 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 733766155919) ^ 34 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_894100824857 : Nat.Prime 894100824857 := by
  apply lucas_primality 894100824857 (3 : ZMod 894100824857)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (389, 1), (1049, 1), (16111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (389, 1), (1049, 1), (16111, 1)] : List FactorBlock).map factorBlockValue).prod) = 894100824857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_389
      · exact prime_oneHundredSixtyTwoFD_1049
      · exact prime_oneHundredSixtyTwoFD_16111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 894100824857) ^ 447050412428 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 894100824857) ^ 52594166168 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 894100824857) ^ 2298459704 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 894100824857) ^ 852336344 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 894100824857) ^ 55496296 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1053880686179 : Nat.Prime 1053880686179 := by
  apply lucas_primality 1053880686179 (2 : ZMod 1053880686179)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (121697, 1), (4329937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (121697, 1), (4329937, 1)] : List FactorBlock).map factorBlockValue).prod) = 1053880686179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_121697
      · exact prime_oneHundredSixtyTwoFD_4329937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1053880686179) ^ 526940343089 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1053880686179) ^ 8659874 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1053880686179) ^ 243394 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1369286193193 : Nat.Prime 1369286193193 := by
  apply lucas_primality 1369286193193 (5 : ZMod 1369286193193)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (197, 1), (289612139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (197, 1), (289612139, 1)] : List FactorBlock).map factorBlockValue).prod) = 1369286193193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_197
      · exact prime_oneHundredSixtyTwoFD_289612139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1369286193193) ^ 684643096596 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1369286193193) ^ 456428731064 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1369286193193) ^ 6950691336 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1369286193193) ^ 4728 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1472950454057 : Nat.Prime 1472950454057 := by
  apply lucas_primality 1472950454057 (3 : ZMod 1472950454057)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (827, 1), (7181761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (827, 1), (7181761, 1)] : List FactorBlock).map factorBlockValue).prod) = 1472950454057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_31
      · exact prime_oneHundredSixtyTwoFD_827
      · exact prime_oneHundredSixtyTwoFD_7181761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1472950454057) ^ 736475227028 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1472950454057) ^ 47514530776 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1472950454057) ^ 1781076728 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1472950454057) ^ 205096 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1800646112479 : Nat.Prime 1800646112479 := by
  apply lucas_primality 1800646112479 (3 : ZMod 1800646112479)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (563, 1), (533050951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (563, 1), (533050951, 1)] : List FactorBlock).map factorBlockValue).prod) = 1800646112479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_563
      · exact prime_oneHundredSixtyTwoFD_533050951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1800646112479) ^ 900323056239 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1800646112479) ^ 600215370826 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1800646112479) ^ 3198305706 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1800646112479) ^ 3378 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1850951952683 : Nat.Prime 1850951952683 := by
  apply lucas_primality 1850951952683 (2 : ZMod 1850951952683)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47279, 1), (2796397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47279, 1), (2796397, 1)] : List FactorBlock).map factorBlockValue).prod) = 1850951952683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_47279
      · exact prime_oneHundredSixtyTwoFD_2796397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1850951952683) ^ 925475976341 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1850951952683) ^ 264421707526 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1850951952683) ^ 39149558 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1850951952683) ^ 661906 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_2460892423277 : Nat.Prime 2460892423277 := by
  apply lucas_primality 2460892423277 (2 : ZMod 2460892423277)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (99137, 1), (886541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (99137, 1), (886541, 1)] : List FactorBlock).map factorBlockValue).prod) = 2460892423277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_99137
      · exact prime_oneHundredSixtyTwoFD_886541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2460892423277) ^ 1230446211638 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2460892423277) ^ 351556060468 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2460892423277) ^ 24823148 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2460892423277) ^ 2775836 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_3058762392017 : Nat.Prime 3058762392017 := by
  apply lucas_primality 3058762392017 (3 : ZMod 3058762392017)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (271, 1), (705434131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (271, 1), (705434131, 1)] : List FactorBlock).map factorBlockValue).prod) = 3058762392017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_271
      · exact prime_oneHundredSixtyTwoFD_705434131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3058762392017) ^ 1529381196008 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3058762392017) ^ 11286946096 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3058762392017) ^ 4336 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_3662228970263 : Nat.Prime 3662228970263 := by
  apply lucas_primality 3662228970263 (5 : ZMod 3662228970263)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (25790344861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (25790344861, 1)] : List FactorBlock).map factorBlockValue).prod) = 3662228970263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_71
      · exact prime_oneHundredSixtyTwoFD_25790344861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3662228970263) ^ 1831114485131 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3662228970263) ^ 51580689722 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3662228970263) ^ 142 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_3687111941479 : Nat.Prime 3687111941479 := by
  apply lucas_primality 3687111941479 (3 : ZMod 3687111941479)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (37, 1), (139568171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (37, 1), (139568171, 1)] : List FactorBlock).map factorBlockValue).prod) = 3687111941479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_37
      · exact prime_oneHundredSixtyTwoFD_139568171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3687111941479) ^ 1843555970739 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 1229037313826 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 526730277354 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 216888937734 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 99651674094 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 26418 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_3797081613103 : Nat.Prime 3797081613103 := by
  apply lucas_primality 3797081613103 (5 : ZMod 3797081613103)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (733813, 1), (862409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (733813, 1), (862409, 1)] : List FactorBlock).map factorBlockValue).prod) = 3797081613103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_733813
      · exact prime_oneHundredSixtyTwoFD_862409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3797081613103) ^ 1898540806551 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3797081613103) ^ 1265693871034 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3797081613103) ^ 5174454 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3797081613103) ^ 4402878 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_5103008119549 : Nat.Prime 5103008119549 := by
  apply lucas_primality 5103008119549 (6 : ZMod 5103008119549)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (4007, 1), (11791883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (4007, 1), (11791883, 1)] : List FactorBlock).map factorBlockValue).prod) = 5103008119549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_4007
      · exact prime_oneHundredSixtyTwoFD_11791883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5103008119549) ^ 2551504059774 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 5103008119549) ^ 1701002706516 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 5103008119549) ^ 1273523364 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 5103008119549) ^ 432756 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_6620306085517 : Nat.Prime 6620306085517 := by
  apply lucas_primality 6620306085517 (7 : ZMod 6620306085517)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (551692173793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (551692173793, 1)] : List FactorBlock).map factorBlockValue).prod) = 6620306085517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_551692173793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6620306085517) ^ 3310153042758 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 6620306085517) ^ 2206768695172 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 6620306085517) ^ 12 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_7104093574121 : Nat.Prime 7104093574121 := by
  apply lucas_primality 7104093574121 (3 : ZMod 7104093574121)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (177602339353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (177602339353, 1)] : List FactorBlock).map factorBlockValue).prod) = 7104093574121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_177602339353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7104093574121) ^ 3552046787060 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 7104093574121) ^ 1420818714824 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 7104093574121) ^ 40 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_11013696930283 : Nat.Prime 11013696930283 := by
  apply lucas_primality 11013696930283 (5 : ZMod 11013696930283)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (347, 1), (23929, 1), (221069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (347, 1), (23929, 1), (221069, 1)] : List FactorBlock).map factorBlockValue).prod) = 11013696930283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_347
      · exact prime_oneHundredSixtyTwoFD_23929
      · exact prime_oneHundredSixtyTwoFD_221069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11013696930283) ^ 5506848465141 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11013696930283) ^ 3671232310094 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11013696930283) ^ 31739760606 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11013696930283) ^ 460265658 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11013696930283) ^ 49820178 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_13971226936099 : Nat.Prime 13971226936099 := by
  apply lucas_primality 13971226936099 (2 : ZMod 13971226936099)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) = 13971226936099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_21617
      · exact prime_oneHundredSixtyTwoFD_6336347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13971226936099) ^ 6985613468049 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 4657075645366 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 821836878594 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 646307394 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 2204934 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_14305552217941 : Nat.Prime 14305552217941 := by
  apply lucas_primality 14305552217941 (2 : ZMod 14305552217941)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (6427, 1), (37097537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (6427, 1), (37097537, 1)] : List FactorBlock).map factorBlockValue).prod) = 14305552217941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_6427
      · exact prime_oneHundredSixtyTwoFD_37097537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14305552217941) ^ 7152776108970 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 4768517405980 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 2861110443588 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 2225852220 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 385620 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_17347431095989 : Nat.Prime 17347431095989 := by
  apply lucas_primality 17347431095989 (2 : ZMod 17347431095989)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (29, 1), (967, 1), (7364299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (29, 1), (967, 1), (7364299, 1)] : List FactorBlock).map factorBlockValue).prod) = 17347431095989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_29
      · exact prime_oneHundredSixtyTwoFD_967
      · exact prime_oneHundredSixtyTwoFD_7364299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17347431095989) ^ 8673715547994 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17347431095989) ^ 5782477031996 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17347431095989) ^ 2478204442284 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17347431095989) ^ 598187279172 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17347431095989) ^ 17939432364 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17347431095989) ^ 2355612 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_18098452556237 : Nat.Prime 18098452556237 := by
  apply lucas_primality 18098452556237 (2 : ZMod 18098452556237)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 2), (26772858811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 2), (26772858811, 1)] : List FactorBlock).map factorBlockValue).prod) = 18098452556237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_26772858811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18098452556237) ^ 9049226278118 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18098452556237) ^ 1392188658172 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18098452556237) ^ 676 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_20902081382297 : Nat.Prime 20902081382297 := by
  apply lucas_primality 20902081382297 (3 : ZMod 20902081382297)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1579, 1), (4423, 1), (374111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1579, 1), (4423, 1), (374111, 1)] : List FactorBlock).map factorBlockValue).prod) = 20902081382297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_1579
      · exact prime_oneHundredSixtyTwoFD_4423
      · exact prime_oneHundredSixtyTwoFD_374111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 20902081382297) ^ 10451040691148 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 20902081382297) ^ 13237543624 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 20902081382297) ^ 4725770152 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 20902081382297) ^ 55871336 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_23580678731417 : Nat.Prime 23580678731417 := by
  apply lucas_primality 23580678731417 (3 : ZMod 23580678731417)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (288689, 1), (10210243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (288689, 1), (10210243, 1)] : List FactorBlock).map factorBlockValue).prod) = 23580678731417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_288689
      · exact prime_oneHundredSixtyTwoFD_10210243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 23580678731417) ^ 11790339365708 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 23580678731417) ^ 81681944 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 23580678731417) ^ 2309512 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_26851715585323 : Nat.Prime 26851715585323 := by
  apply lucas_primality 26851715585323 (2 : ZMod 26851715585323)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (89, 1), (24337, 1), (89833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (89, 1), (24337, 1), (89833, 1)] : List FactorBlock).map factorBlockValue).prod) = 26851715585323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_23
      · exact prime_oneHundredSixtyTwoFD_89
      · exact prime_oneHundredSixtyTwoFD_24337
      · exact prime_oneHundredSixtyTwoFD_89833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26851715585323) ^ 13425857792661 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 26851715585323) ^ 8950571861774 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 26851715585323) ^ 1167465895014 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 26851715585323) ^ 301704669498 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 26851715585323) ^ 1103328906 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 26851715585323) ^ 298907034 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_44108310034367 : Nat.Prime 44108310034367 := by
  apply lucas_primality 44108310034367 (5 : ZMod 44108310034367)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (43, 1), (16544752451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (43, 1), (16544752451, 1)] : List FactorBlock).map factorBlockValue).prod) = 44108310034367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_31
      · exact prime_oneHundredSixtyTwoFD_43
      · exact prime_oneHundredSixtyTwoFD_16544752451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 44108310034367) ^ 22054155017183 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 44108310034367) ^ 1422848710786 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 44108310034367) ^ 1025774651962 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 44108310034367) ^ 2666 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_47
      · exact prime_oneHundredSixtyTwoFD_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_55463448789821 : Nat.Prime 55463448789821 := by
  apply lucas_primality 55463448789821 (2 : ZMod 55463448789821)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (367, 1), (7556328173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (367, 1), (7556328173, 1)] : List FactorBlock).map factorBlockValue).prod) = 55463448789821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_367
      · exact prime_oneHundredSixtyTwoFD_7556328173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55463448789821) ^ 27731724394910 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 55463448789821) ^ 11092689757964 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 55463448789821) ^ 151126563460 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 55463448789821) ^ 7340 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_61128966244483 : Nat.Prime 61128966244483 := by
  apply lucas_primality 61128966244483 (2 : ZMod 61128966244483)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (1193, 1), (3413, 1), (15737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (1193, 1), (3413, 1), (15737, 1)] : List FactorBlock).map factorBlockValue).prod) = 61128966244483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_53
      · exact prime_oneHundredSixtyTwoFD_1193
      · exact prime_oneHundredSixtyTwoFD_3413
      · exact prime_oneHundredSixtyTwoFD_15737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 61128966244483) ^ 30564483122241 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 61128966244483) ^ 20376322081494 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 61128966244483) ^ 1153376721594 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 61128966244483) ^ 51239703474 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 61128966244483) ^ 17910625914 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 61128966244483) ^ 3884410386 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_110926897579643 : Nat.Prime 110926897579643 := by
  apply lucas_primality 110926897579643 (2 : ZMod 110926897579643)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (55463448789821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (55463448789821, 1)] : List FactorBlock).map factorBlockValue).prod) = 110926897579643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_55463448789821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 110926897579643) ^ 55463448789821 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 110926897579643) ^ 2 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_113993486613649 : Nat.Prime 113993486613649 := by
  apply lucas_primality 113993486613649 (7 : ZMod 113993486613649)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (19, 1), (317, 1), (131433079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (19, 1), (317, 1), (131433079, 1)] : List FactorBlock).map factorBlockValue).prod) = 113993486613649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_19
      · exact prime_oneHundredSixtyTwoFD_317
      · exact prime_oneHundredSixtyTwoFD_131433079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 113993486613649) ^ 56996743306824 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 37997828871216 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 5999657190192 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 359600904144 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 867312 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_125314911616211 : Nat.Prime 125314911616211 := by
  apply lucas_primality 125314911616211 (2 : ZMod 125314911616211)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (588383, 1), (21298187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (588383, 1), (21298187, 1)] : List FactorBlock).map factorBlockValue).prod) = 125314911616211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_588383
      · exact prime_oneHundredSixtyTwoFD_21298187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 125314911616211) ^ 62657455808105 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 125314911616211) ^ 25062982323242 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 125314911616211) ^ 212981870 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 125314911616211) ^ 5883830 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_136960286398889 : Nat.Prime 136960286398889 := by
  apply lucas_primality 136960286398889 (3 : ZMod 136960286398889)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (277, 1), (61805183393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (277, 1), (61805183393, 1)] : List FactorBlock).map factorBlockValue).prod) = 136960286398889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_277
      · exact prime_oneHundredSixtyTwoFD_61805183393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 136960286398889) ^ 68480143199444 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 136960286398889) ^ 494441467144 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 136960286398889) ^ 2216 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_148631737990633 : Nat.Prime 148631737990633 := by
  apply lucas_primality 148631737990633 (10 : ZMod 148631737990633)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (47, 1), (691, 1), (14668343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (47, 1), (691, 1), (14668343, 1)] : List FactorBlock).map factorBlockValue).prod) = 148631737990633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_47
      · exact prime_oneHundredSixtyTwoFD_691
      · exact prime_oneHundredSixtyTwoFD_14668343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 148631737990633) ^ 74315868995316 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 49543912663544 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 11433210614664 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 3162377404056 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 215096581752 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 10132824 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_167937736330027 : Nat.Prime 167937736330027 := by
  apply lucas_primality 167937736330027 (2 : ZMod 167937736330027)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 2), (8573, 1), (6439561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 2), (8573, 1), (6439561, 1)] : List FactorBlock).map factorBlockValue).prod) = 167937736330027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_8573
      · exact prime_oneHundredSixtyTwoFD_6439561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 167937736330027) ^ 83968868165013 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 167937736330027) ^ 55979245443342 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 167937736330027) ^ 12918287410002 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 167937736330027) ^ 19589144562 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 167937736330027) ^ 26079066 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_177146449272173 : Nat.Prime 177146449272173 := by
  apply lucas_primality 177146449272173 (2 : ZMod 177146449272173)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (4421, 1), (189006211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (4421, 1), (189006211, 1)] : List FactorBlock).map factorBlockValue).prod) = 177146449272173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_53
      · exact prime_oneHundredSixtyTwoFD_4421
      · exact prime_oneHundredSixtyTwoFD_189006211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 177146449272173) ^ 88573224636086 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 177146449272173) ^ 3342385835324 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 177146449272173) ^ 40069316732 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 177146449272173) ^ 937252 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_203325267622513 : Nat.Prime 203325267622513 := by
  apply lucas_primality 203325267622513 (10 : ZMod 203325267622513)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (605134725067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (605134725067, 1)] : List FactorBlock).map factorBlockValue).prod) = 203325267622513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_605134725067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 203325267622513) ^ 101662633811256 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 203325267622513) ^ 67775089207504 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 203325267622513) ^ 29046466803216 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 203325267622513) ^ 336 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_399270719554739 : Nat.Prime 399270719554739 := by
  apply lucas_primality 399270719554739 (2 : ZMod 399270719554739)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (47, 1), (137018091817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (47, 1), (137018091817, 1)] : List FactorBlock).map factorBlockValue).prod) = 399270719554739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_31
      · exact prime_oneHundredSixtyTwoFD_47
      · exact prime_oneHundredSixtyTwoFD_137018091817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 399270719554739) ^ 199635359777369 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 399270719554739) ^ 12879700630798 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 399270719554739) ^ 8495121692654 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 399270719554739) ^ 2914 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_411794608482007 : Nat.Prime 411794608482007 := by
  apply lucas_primality 411794608482007 (3 : ZMod 411794608482007)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (113, 1), (21577, 1), (278701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (113, 1), (21577, 1), (278701, 1)] : List FactorBlock).map factorBlockValue).prod) = 411794608482007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_101
      · exact prime_oneHundredSixtyTwoFD_113
      · exact prime_oneHundredSixtyTwoFD_21577
      · exact prime_oneHundredSixtyTwoFD_278701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 411794608482007) ^ 205897304241003 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 411794608482007) ^ 137264869494002 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 411794608482007) ^ 4077174341406 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 411794608482007) ^ 3644200075062 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 411794608482007) ^ 19084887078 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 411794608482007) ^ 1477549806 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_465103795143607 : Nat.Prime 465103795143607 := by
  apply lucas_primality 465103795143607 (5 : ZMod 465103795143607)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (193, 1), (125813, 1), (3192389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (193, 1), (125813, 1), (3192389, 1)] : List FactorBlock).map factorBlockValue).prod) = 465103795143607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_193
      · exact prime_oneHundredSixtyTwoFD_125813
      · exact prime_oneHundredSixtyTwoFD_3192389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 465103795143607) ^ 232551897571803 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 465103795143607) ^ 155034598381202 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 465103795143607) ^ 2409864223542 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 465103795143607) ^ 3696786462 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 465103795143607) ^ 145691454 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_486348675716863 : Nat.Prime 486348675716863 := by
  apply lucas_primality 486348675716863 (5 : ZMod 486348675716863)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (109, 1), (251, 1), (1889, 1), (74687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (109, 1), (251, 1), (1889, 1), (74687, 1)] : List FactorBlock).map factorBlockValue).prod) = 486348675716863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_109
      · exact prime_oneHundredSixtyTwoFD_251
      · exact prime_oneHundredSixtyTwoFD_1889
      · exact prime_oneHundredSixtyTwoFD_74687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 486348675716863) ^ 243174337858431 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 486348675716863) ^ 162116225238954 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 486348675716863) ^ 69478382245266 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 486348675716863) ^ 4461914456118 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 486348675716863) ^ 1937644126362 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 486348675716863) ^ 257463565758 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 486348675716863) ^ 6511825026 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_522735672782417 : Nat.Prime 522735672782417 := by
  apply lucas_primality 522735672782417 (3 : ZMod 522735672782417)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (33911, 1), (963433091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (33911, 1), (963433091, 1)] : List FactorBlock).map factorBlockValue).prod) = 522735672782417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_33911
      · exact prime_oneHundredSixtyTwoFD_963433091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 522735672782417) ^ 261367836391208 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 522735672782417) ^ 15414929456 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 522735672782417) ^ 542576 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_729992287516259 : Nat.Prime 729992287516259 := by
  apply lucas_primality 729992287516259 (2 : ZMod 729992287516259)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (19, 1), (2063, 1), (42135017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (19, 1), (2063, 1), (42135017, 1)] : List FactorBlock).map factorBlockValue).prod) = 729992287516259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_19
      · exact prime_oneHundredSixtyTwoFD_2063
      · exact prime_oneHundredSixtyTwoFD_42135017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 729992287516259) ^ 364996143758129 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 729992287516259) ^ 56153252885866 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 729992287516259) ^ 42940722795074 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 729992287516259) ^ 38420646711382 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 729992287516259) ^ 353849872766 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 729992287516259) ^ 17325074 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_829722028640579 : Nat.Prime 829722028640579 := by
  apply lucas_primality 829722028640579 (2 : ZMod 829722028640579)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (14305552217941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (14305552217941, 1)] : List FactorBlock).map factorBlockValue).prod) = 829722028640579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_29
      · exact prime_oneHundredSixtyTwoFD_14305552217941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 829722028640579) ^ 414861014320289 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 829722028640579) ^ 28611104435882 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 829722028640579) ^ 58 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1063991027156509 : Nat.Prime 1063991027156509 := by
  apply lucas_primality 1063991027156509 (2 : ZMod 1063991027156509)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (463, 1), (40487, 1), (143333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (463, 1), (40487, 1), (143333, 1)] : List FactorBlock).map factorBlockValue).prod) = 1063991027156509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_11
      · exact prime_oneHundredSixtyTwoFD_463
      · exact prime_oneHundredSixtyTwoFD_40487
      · exact prime_oneHundredSixtyTwoFD_143333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1063991027156509) ^ 531995513578254 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063991027156509) ^ 354663675718836 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063991027156509) ^ 96726457014228 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063991027156509) ^ 2298036775716 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063991027156509) ^ 26279818884 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063991027156509) ^ 7423210476 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1099435654448473 : Nat.Prime 1099435654448473 := by
  apply lucas_primality 1099435654448473 (5 : ZMod 1099435654448473)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (37, 1), (839, 1), (1217, 1), (110233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (37, 1), (839, 1), (1217, 1), (110233, 1)] : List FactorBlock).map factorBlockValue).prod) = 1099435654448473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_11
      · exact prime_oneHundredSixtyTwoFD_37
      · exact prime_oneHundredSixtyTwoFD_839
      · exact prime_oneHundredSixtyTwoFD_1217
      · exact prime_oneHundredSixtyTwoFD_110233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1099435654448473) ^ 549717827224236 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1099435654448473) ^ 366478551482824 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1099435654448473) ^ 99948695858952 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1099435654448473) ^ 29714477147256 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1099435654448473) ^ 1310411983848 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1099435654448473) ^ 903398237016 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1099435654448473) ^ 9973743384 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1222420807213043 : Nat.Prime 1222420807213043 := by
  apply lucas_primality 1222420807213043 (5 : ZMod 1222420807213043)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (233, 1), (641, 1), (4092387857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (233, 1), (641, 1), (4092387857, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222420807213043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_233
      · exact prime_oneHundredSixtyTwoFD_641
      · exact prime_oneHundredSixtyTwoFD_4092387857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1222420807213043) ^ 611210403606521 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1222420807213043) ^ 5246441232674 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1222420807213043) ^ 1907052741362 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1222420807213043) ^ 298706 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1452722104942727 : Nat.Prime 1452722104942727 := by
  apply lucas_primality 1452722104942727 (5 : ZMod 1452722104942727)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (3687111941479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (3687111941479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1452722104942727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_197
      · exact prime_oneHundredSixtyTwoFD_3687111941479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1452722104942727) ^ 726361052471363 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1452722104942727) ^ 7374223882958 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1452722104942727) ^ 394 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1552976566115003 : Nat.Prime 1552976566115003 := by
  apply lucas_primality 1552976566115003 (2 : ZMod 1552976566115003)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (110926897579643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (110926897579643, 1)] : List FactorBlock).map factorBlockValue).prod) = 1552976566115003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_110926897579643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1552976566115003) ^ 776488283057501 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1552976566115003) ^ 221853795159286 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1552976566115003) ^ 14 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_3516087831827789 : Nat.Prime 3516087831827789 := by
  apply lucas_primality 3516087831827789 (2 : ZMod 3516087831827789)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (30671, 1), (4094244251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (30671, 1), (4094244251, 1)] : List FactorBlock).map factorBlockValue).prod) = 3516087831827789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_30671
      · exact prime_oneHundredSixtyTwoFD_4094244251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3516087831827789) ^ 1758043915913894 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3516087831827789) ^ 502298261689684 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3516087831827789) ^ 114638839028 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3516087831827789) ^ 858788 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_3730576626258283 : Nat.Prime 3730576626258283 := by
  apply lucas_primality 3730576626258283 (2 : ZMod 3730576626258283)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (239, 1), (3607, 1), (14141989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (239, 1), (3607, 1), (14141989, 1)] : List FactorBlock).map factorBlockValue).prod) = 3730576626258283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_239
      · exact prime_oneHundredSixtyTwoFD_3607
      · exact prime_oneHundredSixtyTwoFD_14141989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3730576626258283) ^ 1865288313129141 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3730576626258283) ^ 1243525542086094 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3730576626258283) ^ 219445683897546 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3730576626258283) ^ 15609107222838 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3730576626258283) ^ 1034260223526 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3730576626258283) ^ 263794338 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_4292742240550717 : Nat.Prime 4292742240550717 := by
  apply lucas_primality 4292742240550717 (2 : ZMod 4292742240550717)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4673, 1), (76552219141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4673, 1), (76552219141, 1)] : List FactorBlock).map factorBlockValue).prod) = 4292742240550717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_4673
      · exact prime_oneHundredSixtyTwoFD_76552219141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4292742240550717) ^ 2146371120275358 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4292742240550717) ^ 1430914080183572 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4292742240550717) ^ 918626629692 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4292742240550717) ^ 56076 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_4480938488992579 : Nat.Prime 4480938488992579 := by
  apply lucas_primality 4480938488992579 (3 : ZMod 4480938488992579)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5323, 1), (36781, 1), (3814501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5323, 1), (36781, 1), (3814501, 1)] : List FactorBlock).map factorBlockValue).prod) = 4480938488992579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5323
      · exact prime_oneHundredSixtyTwoFD_36781
      · exact prime_oneHundredSixtyTwoFD_3814501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4480938488992579) ^ 2240469244496289 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4480938488992579) ^ 1493646162997526 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4480938488992579) ^ 841806967686 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4480938488992579) ^ 121827532938 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4480938488992579) ^ 1174711578 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_5584316846200661 : Nat.Prime 5584316846200661 := by
  apply lucas_primality 5584316846200661 (2 : ZMod 5584316846200661)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (20029, 1), (606112099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (20029, 1), (606112099, 1)] : List FactorBlock).map factorBlockValue).prod) = 5584316846200661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_23
      · exact prime_oneHundredSixtyTwoFD_20029
      · exact prime_oneHundredSixtyTwoFD_606112099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5584316846200661) ^ 2792158423100330 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5584316846200661) ^ 1116863369240132 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5584316846200661) ^ 242796384617420 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5584316846200661) ^ 278811565540 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5584316846200661) ^ 9213340 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_6261592457280113 : Nat.Prime 6261592457280113 := by
  apply lucas_primality 6261592457280113 (3 : ZMod 6261592457280113)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (109, 1), (154159, 1), (23289997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (109, 1), (154159, 1), (23289997, 1)] : List FactorBlock).map factorBlockValue).prod) = 6261592457280113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_109
      · exact prime_oneHundredSixtyTwoFD_154159
      · exact prime_oneHundredSixtyTwoFD_23289997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6261592457280113) ^ 3130796228640056 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 6261592457280113) ^ 57445802360368 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 6261592457280113) ^ 40617754768 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 6261592457280113) ^ 268853296 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_6488918974239451 : Nat.Prime 6488918974239451 := by
  apply lucas_primality 6488918974239451 (2 : ZMod 6488918974239451)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (31, 1), (4817, 1), (41385167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (31, 1), (4817, 1), (41385167, 1)] : List FactorBlock).map factorBlockValue).prod) = 6488918974239451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_31
      · exact prime_oneHundredSixtyTwoFD_4817
      · exact prime_oneHundredSixtyTwoFD_41385167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6488918974239451) ^ 3244459487119725 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6488918974239451) ^ 2162972991413150 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6488918974239451) ^ 1297783794847890 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6488918974239451) ^ 926988424891350 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6488918974239451) ^ 209319966910950 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6488918974239451) ^ 1347087185850 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6488918974239451) ^ 156793350 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_7946765611782791 : Nat.Prime 7946765611782791 := by
  apply lucas_primality 7946765611782791 (17 : ZMod 7946765611782791)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (61128966244483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (61128966244483, 1)] : List FactorBlock).map factorBlockValue).prod) = 7946765611782791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_61128966244483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 7946765611782791) ^ 3973382805891395 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 7946765611782791) ^ 1589353122356558 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 7946765611782791) ^ 611289662444830 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 7946765611782791) ^ 130 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_9320616099943403 : Nat.Prime 9320616099943403 := by
  apply lucas_primality 9320616099943403 (2 : ZMod 9320616099943403)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (2927, 1), (3527, 1), (3445999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (2927, 1), (3527, 1), (3445999, 1)] : List FactorBlock).map factorBlockValue).prod) = 9320616099943403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_131
      · exact prime_oneHundredSixtyTwoFD_2927
      · exact prime_oneHundredSixtyTwoFD_3527
      · exact prime_oneHundredSixtyTwoFD_3445999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9320616099943403) ^ 4660308049971701 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9320616099943403) ^ 71149741220942 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9320616099943403) ^ 3184358079926 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9320616099943403) ^ 2642647037126 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9320616099943403) ^ 2704764598 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_10567556260735417 : Nat.Prime 10567556260735417 := by
  apply lucas_primality 10567556260735417 (5 : ZMod 10567556260735417)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (285697, 1), (90658541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (285697, 1), (90658541, 1)] : List FactorBlock).map factorBlockValue).prod) = 10567556260735417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_285697
      · exact prime_oneHundredSixtyTwoFD_90658541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 10567556260735417) ^ 5283778130367708 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 10567556260735417) ^ 3522518753578472 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 10567556260735417) ^ 621620956513848 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 10567556260735417) ^ 36988684728 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 10567556260735417) ^ 116564376 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_14898929285702599 : Nat.Prime 14898929285702599 := by
  apply lucas_primality 14898929285702599 (3 : ZMod 14898929285702599)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (22817, 1), (2654369689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (22817, 1), (2654369689, 1)] : List FactorBlock).map factorBlockValue).prod) = 14898929285702599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_41
      · exact prime_oneHundredSixtyTwoFD_22817
      · exact prime_oneHundredSixtyTwoFD_2654369689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14898929285702599) ^ 7449464642851299 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 14898929285702599) ^ 4966309761900866 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 14898929285702599) ^ 363388519163478 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 14898929285702599) ^ 652974943494 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 14898929285702599) ^ 5612982 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_34893816528424937 : Nat.Prime 34893816528424937 := by
  apply lucas_primality 34893816528424937 (3 : ZMod 34893816528424937)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (241, 1), (18098452556237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (241, 1), (18098452556237, 1)] : List FactorBlock).map factorBlockValue).prod) = 34893816528424937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_241
      · exact prime_oneHundredSixtyTwoFD_18098452556237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 34893816528424937) ^ 17446908264212468 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 34893816528424937) ^ 144787620449896 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 34893816528424937) ^ 1928 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_40377390718990079 : Nat.Prime 40377390718990079 := by
  apply lucas_primality 40377390718990079 (17 : ZMod 40377390718990079)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1552976566115003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1552976566115003, 1)] : List FactorBlock).map factorBlockValue).prod) = 40377390718990079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_1552976566115003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 40377390718990079) ^ 20188695359495039 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 40377390718990079) ^ 3105953132230006 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 40377390718990079) ^ 26 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_44674534769605289 : Nat.Prime 44674534769605289 := by
  apply lucas_primality 44674534769605289 (3 : ZMod 44674534769605289)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5584316846200661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5584316846200661, 1)] : List FactorBlock).map factorBlockValue).prod) = 44674534769605289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5584316846200661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 44674534769605289) ^ 22337267384802644 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 44674534769605289) ^ 8 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_94128405205272079 : Nat.Prime 94128405205272079 := by
  apply lucas_primality 94128405205272079 (6 : ZMod 94128405205272079)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (59, 1), (80317, 1), (174243409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (59, 1), (80317, 1), (174243409, 1)] : List FactorBlock).map factorBlockValue).prod) = 94128405205272079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_19
      · exact prime_oneHundredSixtyTwoFD_59
      · exact prime_oneHundredSixtyTwoFD_80317
      · exact prime_oneHundredSixtyTwoFD_174243409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 94128405205272079) ^ 47064202602636039 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 94128405205272079) ^ 31376135068424026 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 94128405205272079) ^ 4954126589751162 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 94128405205272079) ^ 1595396698394442 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 94128405205272079) ^ 1171961168934 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 94128405205272079) ^ 540212142 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_146134759552611337 : Nat.Prime 146134759552611337 := by
  apply lucas_primality 146134759552611337 (10 : ZMod 146134759552611337)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (13, 1), (17347431095989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (13, 1), (17347431095989, 1)] : List FactorBlock).map factorBlockValue).prod) = 146134759552611337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_17347431095989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 146134759552611337) ^ 73067379776305668 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 146134759552611337) ^ 48711586517537112 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 146134759552611337) ^ 11241135350200872 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 146134759552611337) ^ 8424 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_419996061740133023 : Nat.Prime 419996061740133023 := by
  apply lucas_primality 419996061740133023 (5 : ZMod 419996061740133023)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (882253, 1), (238024728587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (882253, 1), (238024728587, 1)] : List FactorBlock).map factorBlockValue).prod) = 419996061740133023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_882253
      · exact prime_oneHundredSixtyTwoFD_238024728587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 419996061740133023) ^ 209998030870066511 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 419996061740133023) ^ 476049457174 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 419996061740133023) ^ 1764506 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_455539386926208391 : Nat.Prime 455539386926208391 := by
  apply lucas_primality 455539386926208391 (3 : ZMod 455539386926208391)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 2), (61, 1), (1472950454057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 2), (61, 1), (1472950454057, 1)] : List FactorBlock).map factorBlockValue).prod) = 455539386926208391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_61
      · exact prime_oneHundredSixtyTwoFD_1472950454057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 455539386926208391) ^ 227769693463104195 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 455539386926208391) ^ 151846462308736130 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 455539386926208391) ^ 91107877385241678 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 455539386926208391) ^ 35041491302016030 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 455539386926208391) ^ 7467858802068990 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 455539386926208391) ^ 309270 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_618877695587683109 : Nat.Prime 618877695587683109 := by
  apply lucas_primality 618877695587683109 (2 : ZMod 618877695587683109)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 1), (367, 1), (19141, 1), (202063399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 1), (367, 1), (19141, 1), (202063399, 1)] : List FactorBlock).map factorBlockValue).prod) = 618877695587683109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_109
      · exact prime_oneHundredSixtyTwoFD_367
      · exact prime_oneHundredSixtyTwoFD_19141
      · exact prime_oneHundredSixtyTwoFD_202063399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 618877695587683109) ^ 309438847793841554 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 618877695587683109) ^ 5677777023740212 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 618877695587683109) ^ 1686315246832924 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 618877695587683109) ^ 32332568600788 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 618877695587683109) ^ 3062789692 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_686544918352552681 : Nat.Prime 686544918352552681 := by
  apply lucas_primality 686544918352552681 (23 : ZMod 686544918352552681)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7579493, 1), (754827223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7579493, 1), (754827223, 1)] : List FactorBlock).map factorBlockValue).prod) = 686544918352552681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_7579493
      · exact prime_oneHundredSixtyTwoFD_754827223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 686544918352552681) ^ 343272459176276340 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (23 : ZMod 686544918352552681) ^ 228848306117517560 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (23 : ZMod 686544918352552681) ^ 137308983670510536 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (23 : ZMod 686544918352552681) ^ 90579266760 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (23 : ZMod 686544918352552681) ^ 909539160 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_872002404010526741 : Nat.Prime 872002404010526741 := by
  apply lucas_primality 872002404010526741 (11 : ZMod 872002404010526741)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 4), (18701, 1), (971025637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 4), (18701, 1), (971025637, 1)] : List FactorBlock).map factorBlockValue).prod) = 872002404010526741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_18701
      · exact prime_oneHundredSixtyTwoFD_971025637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 872002404010526741) ^ 436001202005263370 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 872002404010526741) ^ 174400480802105348 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 872002404010526741) ^ 124571772001503820 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 872002404010526741) ^ 46628651088740 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 872002404010526741) ^ 898022020 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_969057377255761897 : Nat.Prime 969057377255761897 := by
  apply lucas_primality 969057377255761897 (7 : ZMod 969057377255761897)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (40377390718990079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (40377390718990079, 1)] : List FactorBlock).map factorBlockValue).prod) = 969057377255761897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_40377390718990079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 969057377255761897) ^ 484528688627880948 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 969057377255761897) ^ 323019125751920632 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 969057377255761897) ^ 24 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1608309624659490097 : Nat.Prime 1608309624659490097 := by
  apply lucas_primality 1608309624659490097 (5 : ZMod 1608309624659490097)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (40487, 1), (160907, 1), (5143253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (40487, 1), (160907, 1), (5143253, 1)] : List FactorBlock).map factorBlockValue).prod) = 1608309624659490097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_40487
      · exact prime_oneHundredSixtyTwoFD_160907
      · exact prime_oneHundredSixtyTwoFD_5143253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1608309624659490097) ^ 804154812329745048 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1608309624659490097) ^ 536103208219830032 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1608309624659490097) ^ 39724099702608 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1608309624659490097) ^ 9995274442128 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1608309624659490097) ^ 312702802032 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1612797799865644963 : Nat.Prime 1612797799865644963 := by
  apply lucas_primality 1612797799865644963 (2 : ZMod 1612797799865644963)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (150203, 1), (20569835207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (150203, 1), (20569835207, 1)] : List FactorBlock).map factorBlockValue).prod) = 1612797799865644963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_29
      · exact prime_oneHundredSixtyTwoFD_150203
      · exact prime_oneHundredSixtyTwoFD_20569835207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1612797799865644963) ^ 806398899932822481 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1612797799865644963) ^ 537599266621881654 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1612797799865644963) ^ 55613717236746378 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1612797799865644963) ^ 10737453978054 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1612797799865644963) ^ 78405966 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1881806295833552119 : Nat.Prime 1881806295833552119 := by
  apply lucas_primality 1881806295833552119 (11 : ZMod 1881806295833552119)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (277, 1), (349, 1), (98507, 1), (32934523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (277, 1), (349, 1), (98507, 1), (32934523, 1)] : List FactorBlock).map factorBlockValue).prod) = 1881806295833552119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_277
      · exact prime_oneHundredSixtyTwoFD_349
      · exact prime_oneHundredSixtyTwoFD_98507
      · exact prime_oneHundredSixtyTwoFD_32934523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1881806295833552119) ^ 940903147916776059 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1881806295833552119) ^ 627268765277850706 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1881806295833552119) ^ 6793524533695134 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1881806295833552119) ^ 5391995117001582 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1881806295833552119) ^ 19103274851874 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1881806295833552119) ^ 57137803266 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1901048408298370901 : Nat.Prime 1901048408298370901 := by
  apply lucas_primality 1901048408298370901 (2 : ZMod 1901048408298370901)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (17, 1), (23, 1), (193, 1), (474571, 1), (530833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (17, 1), (23, 1), (193, 1), (474571, 1), (530833, 1)] : List FactorBlock).map factorBlockValue).prod) = 1901048408298370901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_23
      · exact prime_oneHundredSixtyTwoFD_193
      · exact prime_oneHundredSixtyTwoFD_474571
      · exact prime_oneHundredSixtyTwoFD_530833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1901048408298370901) ^ 950524204149185450 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1901048408298370901) ^ 380209681659674180 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1901048408298370901) ^ 111826376958727700 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1901048408298370901) ^ 82654278621668300 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1901048408298370901) ^ 9849991752841300 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1901048408298370901) ^ 4005825067900 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1901048408298370901) ^ 3581255137300 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_101
      · exact prime_oneHundredSixtyTwoFD_191
      · exact prime_oneHundredSixtyTwoFD_48017
      · exact prime_oneHundredSixtyTwoFD_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_4755315234808230821 : Nat.Prime 4755315234808230821 := by
  apply lucas_primality 4755315234808230821 (2 : ZMod 4755315234808230821)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (7127, 1), (34273, 1), (10696681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (7127, 1), (34273, 1), (10696681, 1)] : List FactorBlock).map factorBlockValue).prod) = 4755315234808230821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_7127
      · exact prime_oneHundredSixtyTwoFD_34273
      · exact prime_oneHundredSixtyTwoFD_10696681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4755315234808230821) ^ 2377657617404115410 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4755315234808230821) ^ 951063046961646164 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4755315234808230821) ^ 679330747829747260 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4755315234808230821) ^ 365793479600633140 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4755315234808230821) ^ 667225373201660 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4755315234808230821) ^ 138748146786340 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4755315234808230821) ^ 444559881220 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_5044842754105674733 : Nat.Prime 5044842754105674733 := by
  apply lucas_primality 5044842754105674733 (6 : ZMod 5044842754105674733)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (20113, 1), (20902081382297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (20113, 1), (20902081382297, 1)] : List FactorBlock).map factorBlockValue).prod) = 5044842754105674733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_20113
      · exact prime_oneHundredSixtyTwoFD_20902081382297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5044842754105674733) ^ 2522421377052837366 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 5044842754105674733) ^ 1681614251368558244 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 5044842754105674733) ^ 250824976587564 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 5044842754105674733) ^ 241356 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_6017562937482896693 : Nat.Prime 6017562937482896693 := by
  apply lucas_primality 6017562937482896693 (2 : ZMod 6017562937482896693)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (4091299, 1), (2806907717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (4091299, 1), (2806907717, 1)] : List FactorBlock).map factorBlockValue).prod) = 6017562937482896693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_131
      · exact prime_oneHundredSixtyTwoFD_4091299
      · exact prime_oneHundredSixtyTwoFD_2806907717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6017562937482896693) ^ 3008781468741448346 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6017562937482896693) ^ 45935594942617532 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6017562937482896693) ^ 1470819643708 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6017562937482896693) ^ 2143840676 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_11324793704342693983 : Nat.Prime 11324793704342693983 := by
  apply lucas_primality 11324793704342693983 (3 : ZMod 11324793704342693983)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (191911, 1), (894100824857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (191911, 1), (894100824857, 1)] : List FactorBlock).map factorBlockValue).prod) = 11324793704342693983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_11
      · exact prime_oneHundredSixtyTwoFD_191911
      · exact prime_oneHundredSixtyTwoFD_894100824857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11324793704342693983) ^ 5662396852171346991 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 11324793704342693983) ^ 3774931234780897994 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 11324793704342693983) ^ 1029526700394790362 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 11324793704342693983) ^ 59010654440562 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 11324793704342693983) ^ 12666126 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_20179371016422698933 : Nat.Prime 20179371016422698933 := by
  apply lucas_primality 20179371016422698933 (2 : ZMod 20179371016422698933)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5044842754105674733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5044842754105674733, 1)] : List FactorBlock).map factorBlockValue).prod) = 20179371016422698933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5044842754105674733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 20179371016422698933) ^ 10089685508211349466 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 20179371016422698933) ^ 4 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_35666719808417469181 : Nat.Prime 35666719808417469181 := by
  apply lucas_primality 35666719808417469181 (2 : ZMod 35666719808417469181)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (2801, 1), (23580678731417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (2801, 1), (23580678731417, 1)] : List FactorBlock).map factorBlockValue).prod) = 35666719808417469181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_2801
      · exact prime_oneHundredSixtyTwoFD_23580678731417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35666719808417469181) ^ 17833359904208734590 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 35666719808417469181) ^ 11888906602805823060 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 35666719808417469181) ^ 7133343961683493836 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 35666719808417469181) ^ 12733566514965180 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 35666719808417469181) ^ 1512540 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_56538692335790847121 : Nat.Prime 56538692335790847121 := by
  apply lucas_primality 56538692335790847121 (17 : ZMod 56538692335790847121)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (67, 1), (3516087831827789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (67, 1), (3516087831827789, 1)] : List FactorBlock).map factorBlockValue).prod) = 56538692335790847121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_67
      · exact prime_oneHundredSixtyTwoFD_3516087831827789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 56538692335790847121) ^ 28269346167895423560 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 56538692335790847121) ^ 18846230778596949040 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 56538692335790847121) ^ 11307738467158169424 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 56538692335790847121) ^ 843861079638669360 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (17 : ZMod 56538692335790847121) ^ 16080 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_98103846261021787661 : Nat.Prime 98103846261021787661 := by
  apply lucas_primality 98103846261021787661 (2 : ZMod 98103846261021787661)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (293, 1), (523, 1), (2963, 1), (10803266219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (293, 1), (523, 1), (2963, 1), (10803266219, 1)] : List FactorBlock).map factorBlockValue).prod) = 98103846261021787661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_293
      · exact prime_oneHundredSixtyTwoFD_523
      · exact prime_oneHundredSixtyTwoFD_2963
      · exact prime_oneHundredSixtyTwoFD_10803266219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 98103846261021787661) ^ 49051923130510893830 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 98103846261021787661) ^ 19620769252204357532 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 98103846261021787661) ^ 334825413860142620 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 98103846261021787661) ^ 187579055948416420 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 98103846261021787661) ^ 33109634242666820 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 98103846261021787661) ^ 9080943140 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_100632140597689014949 : Nat.Prime 100632140597689014949 := by
  apply lucas_primality 100632140597689014949 (2 : ZMod 100632140597689014949)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (857, 1), (82775113, 1), (118215619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (857, 1), (82775113, 1), (118215619, 1)] : List FactorBlock).map factorBlockValue).prod) = 100632140597689014949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_857
      · exact prime_oneHundredSixtyTwoFD_82775113
      · exact prime_oneHundredSixtyTwoFD_118215619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 100632140597689014949) ^ 50316070298844507474 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 100632140597689014949) ^ 33544046865896338316 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 100632140597689014949) ^ 117423734653079364 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 100632140597689014949) ^ 1215729425796 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 100632140597689014949) ^ 851259262092 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_120435602933347335617 : Nat.Prime 120435602933347335617 := by
  apply lucas_primality 120435602933347335617 (3 : ZMod 120435602933347335617)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (1881806295833552119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (1881806295833552119, 1)] : List FactorBlock).map factorBlockValue).prod) = 120435602933347335617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_1881806295833552119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 120435602933347335617) ^ 60217801466673667808 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 120435602933347335617) ^ 64 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_123442633682500070513 : Nat.Prime 123442633682500070513 := by
  apply lucas_primality 123442633682500070513 (5 : ZMod 123442633682500070513)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (47, 1), (101, 1), (383, 1), (419, 1), (20681, 1), (69959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (47, 1), (101, 1), (383, 1), (419, 1), (20681, 1), (69959, 1)] : List FactorBlock).map factorBlockValue).prod) = 123442633682500070513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_47
      · exact prime_oneHundredSixtyTwoFD_101
      · exact prime_oneHundredSixtyTwoFD_383
      · exact prime_oneHundredSixtyTwoFD_419
      · exact prime_oneHundredSixtyTwoFD_20681
      · exact prime_oneHundredSixtyTwoFD_69959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 123442633682500070513) ^ 61721316841250035256 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 123442633682500070513) ^ 17634661954642867216 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 123442633682500070513) ^ 2626439014521278096 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 123442633682500070513) ^ 1222204293886139312 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 123442633682500070513) ^ 322304526586162064 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 123442633682500070513) ^ 294612490889021648 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 123442633682500070513) ^ 5968890947367152 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 123442633682500070513) ^ 1764499688138768 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_133428789850506403081 : Nat.Prime 133428789850506403081 := by
  apply lucas_primality 133428789850506403081 (7 : ZMod 133428789850506403081)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (42379, 1), (48571, 1), (540182551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (42379, 1), (48571, 1), (540182551, 1)] : List FactorBlock).map factorBlockValue).prod) = 133428789850506403081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_42379
      · exact prime_oneHundredSixtyTwoFD_48571
      · exact prime_oneHundredSixtyTwoFD_540182551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 133428789850506403081) ^ 66714394925253201540 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 133428789850506403081) ^ 44476263283502134360 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 133428789850506403081) ^ 26685757970101280616 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 133428789850506403081) ^ 3148464802154520 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 133428789850506403081) ^ 2747087559459480 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 133428789850506403081) ^ 247006849080 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_141948996516209640817 : Nat.Prime 141948996516209640817 := by
  apply lucas_primality 141948996516209640817 (5 : ZMod 141948996516209640817)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (23, 1), (2011, 1), (7104093574121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (23, 1), (2011, 1), (7104093574121, 1)] : List FactorBlock).map factorBlockValue).prod) = 141948996516209640817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_23
      · exact prime_oneHundredSixtyTwoFD_2011
      · exact prime_oneHundredSixtyTwoFD_7104093574121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 141948996516209640817) ^ 70974498258104820408 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 141948996516209640817) ^ 47316332172069880272 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 141948996516209640817) ^ 6171695500704766992 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 141948996516209640817) ^ 70586273752466256 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 141948996516209640817) ^ 19981296 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_206076508764416615329 : Nat.Prime 206076508764416615329 := by
  apply lucas_primality 206076508764416615329 (67 : ZMod 206076508764416615329)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (1053156017, 1), (2038283279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (1053156017, 1), (2038283279, 1)] : List FactorBlock).map factorBlockValue).prod) = 206076508764416615329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_1053156017
      · exact prime_oneHundredSixtyTwoFD_2038283279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (67 : ZMod 206076508764416615329) ^ 103038254382208307664 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (67 : ZMod 206076508764416615329) ^ 68692169588138871776 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (67 : ZMod 206076508764416615329) ^ 195675194784 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (67 : ZMod 206076508764416615329) ^ 101102977632 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_207047002757334706501 : Nat.Prime 207047002757334706501 := by
  apply lucas_primality 207047002757334706501 (10 : ZMod 207047002757334706501)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (37, 1), (3730576626258283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (37, 1), (3730576626258283, 1)] : List FactorBlock).map factorBlockValue).prod) = 207047002757334706501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_37
      · exact prime_oneHundredSixtyTwoFD_3730576626258283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 207047002757334706501) ^ 103523501378667353250 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 207047002757334706501) ^ 69015667585778235500 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 207047002757334706501) ^ 41409400551466941300 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 207047002757334706501) ^ 5595864939387424500 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 207047002757334706501) ^ 55500 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_218893645606608292673 : Nat.Prime 218893645606608292673 := by
  apply lucas_primality 218893645606608292673 (3 : ZMod 218893645606608292673)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (11, 1), (19, 1), (29, 1), (1287197, 1), (438393269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (11, 1), (19, 1), (29, 1), (1287197, 1), (438393269, 1)] : List FactorBlock).map factorBlockValue).prod) = 218893645606608292673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_11
      · exact prime_oneHundredSixtyTwoFD_19
      · exact prime_oneHundredSixtyTwoFD_29
      · exact prime_oneHundredSixtyTwoFD_1287197
      · exact prime_oneHundredSixtyTwoFD_438393269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 218893645606608292673) ^ 109446822803304146336 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 218893645606608292673) ^ 19899422327873481152 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 218893645606608292673) ^ 11520718189821489088 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 218893645606608292673) ^ 7548056745055458368 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 218893645606608292673) ^ 170054502618176 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 218893645606608292673) ^ 499308865088 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_6863
      · exact prime_oneHundredSixtyTwoFD_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_277150409895147902543 : Nat.Prime 277150409895147902543 := by
  apply lucas_primality 277150409895147902543 (5 : ZMod 277150409895147902543)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (969057377255761897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (969057377255761897, 1)] : List FactorBlock).map factorBlockValue).prod) = 277150409895147902543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_11
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_969057377255761897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 277150409895147902543) ^ 138575204947573951271 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 277150409895147902543) ^ 25195491808649809322 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 277150409895147902543) ^ 21319262299626761734 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 277150409895147902543) ^ 286 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_303652137242507412901 : Nat.Prime 303652137242507412901 := by
  apply lucas_primality 303652137242507412901 (2 : ZMod 303652137242507412901)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (307, 1), (1831, 1), (1800646112479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (307, 1), (1831, 1), (1800646112479, 1)] : List FactorBlock).map factorBlockValue).prod) = 303652137242507412901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_307
      · exact prime_oneHundredSixtyTwoFD_1831
      · exact prime_oneHundredSixtyTwoFD_1800646112479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 303652137242507412901) ^ 151826068621253706450 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 303652137242507412901) ^ 101217379080835804300 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 303652137242507412901) ^ 60730427448501482580 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 303652137242507412901) ^ 989094909584714700 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 303652137242507412901) ^ 165839506959315900 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 303652137242507412901) ^ 168635100 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_535026560709385213837 : Nat.Prime 535026560709385213837 := by
  apply lucas_primality 535026560709385213837 (2 : ZMod 535026560709385213837)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (24907, 1), (154937, 1), (679623851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (24907, 1), (154937, 1), (679623851, 1)] : List FactorBlock).map factorBlockValue).prod) = 535026560709385213837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_24907
      · exact prime_oneHundredSixtyTwoFD_154937
      · exact prime_oneHundredSixtyTwoFD_679623851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 535026560709385213837) ^ 267513280354692606918 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 535026560709385213837) ^ 178342186903128404612 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 535026560709385213837) ^ 31472150629963836108 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 535026560709385213837) ^ 21480971642886948 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 535026560709385213837) ^ 3453187816398828 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 535026560709385213837) ^ 787239235236 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1146250422224934728417 : Nat.Prime 1146250422224934728417 := by
  apply lucas_primality 1146250422224934728417 (3 : ZMod 1146250422224934728417)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (13, 1), (23, 1), (7573, 1), (1154401, 1), (1245779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (13, 1), (23, 1), (7573, 1), (1154401, 1), (1245779, 1)] : List FactorBlock).map factorBlockValue).prod) = 1146250422224934728417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_11
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_23
      · exact prime_oneHundredSixtyTwoFD_7573
      · exact prime_oneHundredSixtyTwoFD_1154401
      · exact prime_oneHundredSixtyTwoFD_1245779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1146250422224934728417) ^ 573125211112467364208 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 104204583838630429856 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 88173109401918056032 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 49836974879344988192 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 151360150828592992 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 992939561058016 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 920107356300704 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_10972656432056158334449 : Nat.Prime 10972656432056158334449 := by
  apply lucas_primality 10972656432056158334449 (7 : ZMod 10972656432056158334449)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (127, 1), (3701, 1), (486348675716863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (127, 1), (3701, 1), (486348675716863, 1)] : List FactorBlock).map factorBlockValue).prod) = 10972656432056158334449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_127
      · exact prime_oneHundredSixtyTwoFD_3701
      · exact prime_oneHundredSixtyTwoFD_486348675716863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 10972656432056158334449) ^ 5486328216028079167224 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 10972656432056158334449) ^ 3657552144018719444816 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 10972656432056158334449) ^ 86398869543749278224 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 10972656432056158334449) ^ 2964781527169996848 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 10972656432056158334449) ^ 22561296 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_16808179182239715252613 : Nat.Prime 16808179182239715252613 := by
  apply lucas_primality 16808179182239715252613 (5 : ZMod 16808179182239715252613)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (114967, 1), (2471461, 1), (704229839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (114967, 1), (2471461, 1), (704229839, 1)] : List FactorBlock).map factorBlockValue).prod) = 16808179182239715252613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_114967
      · exact prime_oneHundredSixtyTwoFD_2471461
      · exact prime_oneHundredSixtyTwoFD_704229839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 16808179182239715252613) ^ 8404089591119857626306 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 16808179182239715252613) ^ 5602726394079905084204 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 16808179182239715252613) ^ 2401168454605673607516 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 16808179182239715252613) ^ 146200032898481436 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 16808179182239715252613) ^ 6800908119626292 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 16808179182239715252613) ^ 23867462370108 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_31588916790240203799011 : Nat.Prime 31588916790240203799011 := by
  apply lucas_primality 31588916790240203799011 (6 : ZMod 31588916790240203799011)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (70709, 1), (44674534769605289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (70709, 1), (44674534769605289, 1)] : List FactorBlock).map factorBlockValue).prod) = 31588916790240203799011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_70709
      · exact prime_oneHundredSixtyTwoFD_44674534769605289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 31588916790240203799011) ^ 15794458395120101899505 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 31588916790240203799011) ^ 6317783358048040759802 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 31588916790240203799011) ^ 446745347696052890 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 31588916790240203799011) ^ 707090 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_36020595815294828169863 : Nat.Prime 36020595815294828169863 := by
  apply lucas_primality 36020595815294828169863 (5 : ZMod 36020595815294828169863)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (211, 1), (313, 1), (379, 1), (1823, 1), (37987, 1), (10390423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (211, 1), (313, 1), (379, 1), (1823, 1), (37987, 1), (10390423, 1)] : List FactorBlock).map factorBlockValue).prod) = 36020595815294828169863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_211
      · exact prime_oneHundredSixtyTwoFD_313
      · exact prime_oneHundredSixtyTwoFD_379
      · exact prime_oneHundredSixtyTwoFD_1823
      · exact prime_oneHundredSixtyTwoFD_37987
      · exact prime_oneHundredSixtyTwoFD_10390423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36020595815294828169863) ^ 18010297907647414084931 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 36020595815294828169863) ^ 170713724243103451042 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 36020595815294828169863) ^ 115081775767715105974 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 36020595815294828169863) ^ 95041149908429625778 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 36020595815294828169863) ^ 19758966437353169594 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 36020595815294828169863) ^ 948234812311970626 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 36020595815294828169863) ^ 3466711202738794 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_50435018577897128050349 : Nat.Prime 50435018577897128050349 := by
  apply lucas_primality 50435018577897128050349 (2 : ZMod 50435018577897128050349)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1146250422224934728417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1146250422224934728417, 1)] : List FactorBlock).map factorBlockValue).prod) = 50435018577897128050349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_11
      · exact prime_oneHundredSixtyTwoFD_1146250422224934728417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 50435018577897128050349) ^ 25217509288948564025174 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 50435018577897128050349) ^ 4585001688899738913668 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 50435018577897128050349) ^ 44 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_54537434617677819649091 : Nat.Prime 54537434617677819649091 := by
  apply lucas_primality 54537434617677819649091 (2 : ZMod 54537434617677819649091)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2699, 1), (124058861, 1), (16287860131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2699, 1), (124058861, 1), (16287860131, 1)] : List FactorBlock).map factorBlockValue).prod) = 54537434617677819649091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_2699
      · exact prime_oneHundredSixtyTwoFD_124058861
      · exact prime_oneHundredSixtyTwoFD_16287860131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 54537434617677819649091) ^ 27268717308838909824545 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 54537434617677819649091) ^ 10907486923535563929818 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 54537434617677819649091) ^ 20206533759791707910 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 54537434617677819649091) ^ 439609344935690 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 54537434617677819649091) ^ 3348348658390 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_63390542822135290026541 : Nat.Prime 63390542822135290026541 := by
  apply lucas_primality 63390542822135290026541 (7 : ZMod 63390542822135290026541)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (11, 1), (19, 1), (1367, 1), (136960286398889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (11, 1), (19, 1), (1367, 1), (136960286398889, 1)] : List FactorBlock).map factorBlockValue).prod) = 63390542822135290026541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_11
      · exact prime_oneHundredSixtyTwoFD_19
      · exact prime_oneHundredSixtyTwoFD_1367
      · exact prime_oneHundredSixtyTwoFD_136960286398889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 63390542822135290026541) ^ 31695271411067645013270 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 63390542822135290026541) ^ 21130180940711763342180 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 63390542822135290026541) ^ 12678108564427058005308 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 63390542822135290026541) ^ 5762776620194117275140 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 63390542822135290026541) ^ 3336344359059752106660 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 63390542822135290026541) ^ 46372013768935837620 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 63390542822135290026541) ^ 462838860 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_81931948070940510573853 : Nat.Prime 81931948070940510573853 := by
  apply lucas_primality 81931948070940510573853 (6 : ZMod 81931948070940510573853)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (41, 1), (67, 1), (193, 1), (4292742240550717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (41, 1), (67, 1), (193, 1), (4292742240550717, 1)] : List FactorBlock).map factorBlockValue).prod) = 81931948070940510573853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_41
      · exact prime_oneHundredSixtyTwoFD_67
      · exact prime_oneHundredSixtyTwoFD_193
      · exact prime_oneHundredSixtyTwoFD_4292742240550717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 81931948070940510573853) ^ 40965974035470255286926 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 81931948070940510573853) ^ 27310649356980170191284 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 81931948070940510573853) ^ 1998340196852207574972 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 81931948070940510573853) ^ 1222864896581201650356 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 81931948070940510573853) ^ 424517865652541505564 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 81931948070940510573853) ^ 19086156 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_94824147372238166988977 : Nat.Prime 94824147372238166988977 := by
  apply lucas_primality 94824147372238166988977 (3 : ZMod 94824147372238166988977)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (103, 1), (3232393, 1), (1369286193193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (103, 1), (3232393, 1), (1369286193193, 1)] : List FactorBlock).map factorBlockValue).prod) = 94824147372238166988977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_103
      · exact prime_oneHundredSixtyTwoFD_3232393
      · exact prime_oneHundredSixtyTwoFD_1369286193193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 94824147372238166988977) ^ 47412073686119083494488 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 94824147372238166988977) ^ 7294165182479858999152 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 94824147372238166988977) ^ 920622790021729776592 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 94824147372238166988977) ^ 29335587402966832 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 94824147372238166988977) ^ 69250787632 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_215918951408411223998251 : Nat.Prime 215918951408411223998251 := by
  apply lucas_primality 215918951408411223998251 (3 : ZMod 215918951408411223998251)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 3), (1009, 1), (10567556260735417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 3), (1009, 1), (10567556260735417, 1)] : List FactorBlock).map factorBlockValue).prod) = 215918951408411223998251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_1009
      · exact prime_oneHundredSixtyTwoFD_10567556260735417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 215918951408411223998251) ^ 107959475704205611999125 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 215918951408411223998251) ^ 71972983802803741332750 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 215918951408411223998251) ^ 43183790281682244799650 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 215918951408411223998251) ^ 213993014279892194250 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 215918951408411223998251) ^ 20432250 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_288520672202247931694107 : Nat.Prime 288520672202247931694107 := by
  apply lucas_primality 288520672202247931694107 (2 : ZMod 288520672202247931694107)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (79423, 1), (4735909, 1), (1800601883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (79423, 1), (4735909, 1), (1800601883, 1)] : List FactorBlock).map factorBlockValue).prod) = 288520672202247931694107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_71
      · exact prime_oneHundredSixtyTwoFD_79423
      · exact prime_oneHundredSixtyTwoFD_4735909
      · exact prime_oneHundredSixtyTwoFD_1800601883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 288520672202247931694107) ^ 144260336101123965847053 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 288520672202247931694107) ^ 96173557400749310564702 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 288520672202247931694107) ^ 4063671439468280728086 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 288520672202247931694107) ^ 3632709318487691622 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 288520672202247931694107) ^ 60921920628594834 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 288520672202247931694107) ^ 160235682815982 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_377021374415911057767289 : Nat.Prime 377021374415911057767289 := by
  apply lucas_primality 377021374415911057767289 (7 : ZMod 377021374415911057767289)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5783, 1), (59509, 1), (99871, 1), (457066601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5783, 1), (59509, 1), (99871, 1), (457066601, 1)] : List FactorBlock).map factorBlockValue).prod) = 377021374415911057767289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5783
      · exact prime_oneHundredSixtyTwoFD_59509
      · exact prime_oneHundredSixtyTwoFD_99871
      · exact prime_oneHundredSixtyTwoFD_457066601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 377021374415911057767289) ^ 188510687207955528883644 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 377021374415911057767289) ^ 125673791471970352589096 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 377021374415911057767289) ^ 65194773372974417736 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 377021374415911057767289) ^ 6335535371387707032 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 377021374415911057767289) ^ 3775083602005697928 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 377021374415911057767289) ^ 824871853666488 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_421226894041107731343491 : Nat.Prime 421226894041107731343491 := by
  apply lucas_primality 421226894041107731343491 (2 : ZMod 421226894041107731343491)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (66373, 1), (85621, 1), (157705373099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (66373, 1), (85621, 1), (157705373099, 1)] : List FactorBlock).map factorBlockValue).prod) = 421226894041107731343491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_47
      · exact prime_oneHundredSixtyTwoFD_66373
      · exact prime_oneHundredSixtyTwoFD_85621
      · exact prime_oneHundredSixtyTwoFD_157705373099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 421226894041107731343491) ^ 210613447020553865671745 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 84245378808221546268698 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 8962274341300164496670 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 6346359122551455130 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 4919668002488965690 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 2670973637510 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_878899926231809511221431 : Nat.Prime 878899926231809511221431 := by
  apply lucas_primality 878899926231809511221431 (6 : ZMod 878899926231809511221431)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) = 878899926231809511221431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_797
      · exact prime_oneHundredSixtyTwoFD_125287
      · exact prime_oneHundredSixtyTwoFD_13971226936099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 878899926231809511221431) ^ 439449963115904755610715 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 292966642077269837073810 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 175779985246361902244286 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 125557132318829930174490 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 1102760258760112310190 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 7015092756884668890 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 62907855570 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_986694323964026754195253 : Nat.Prime 986694323964026754195253 := by
  apply lucas_primality 986694323964026754195253 (29 : ZMod 986694323964026754195253)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (19, 1), (206076508764416615329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (19, 1), (206076508764416615329, 1)] : List FactorBlock).map factorBlockValue).prod) = 986694323964026754195253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_19
      · exact prime_oneHundredSixtyTwoFD_206076508764416615329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 986694323964026754195253) ^ 493347161982013377097626 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (29 : ZMod 986694323964026754195253) ^ 328898107988008918065084 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (29 : ZMod 986694323964026754195253) ^ 140956331994860964885036 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (29 : ZMod 986694323964026754195253) ^ 51931280208632987062908 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (29 : ZMod 986694323964026754195253) ^ 4788 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_2032119206627662952327221 : Nat.Prime 2032119206627662952327221 := by
  apply lucas_primality 2032119206627662952327221 (10 : ZMod 2032119206627662952327221)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (420241, 1), (11958103, 1), (87527897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (420241, 1), (11958103, 1), (87527897, 1)] : List FactorBlock).map factorBlockValue).prod) = 2032119206627662952327221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_11
      · exact prime_oneHundredSixtyTwoFD_420241
      · exact prime_oneHundredSixtyTwoFD_11958103
      · exact prime_oneHundredSixtyTwoFD_87527897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2032119206627662952327221) ^ 1016059603313831476163610 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 2032119206627662952327221) ^ 677373068875887650775740 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 2032119206627662952327221) ^ 406423841325532590465444 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 2032119206627662952327221) ^ 290302743803951850332460 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 2032119206627662952327221) ^ 184738109693423904757020 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 2032119206627662952327221) ^ 4835604347571186420 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 2032119206627662952327221) ^ 169936586649877740 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (10 : ZMod 2032119206627662952327221) ^ 23216817452242260 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_3085019010432118828936111 : Nat.Prime 3085019010432118828936111 := by
  apply lucas_primality 3085019010432118828936111 (3 : ZMod 3085019010432118828936111)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (22949203, 1), (4480938488992579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (22949203, 1), (4480938488992579, 1)] : List FactorBlock).map factorBlockValue).prod) = 3085019010432118828936111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_22949203
      · exact prime_oneHundredSixtyTwoFD_4480938488992579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3085019010432118828936111) ^ 1542509505216059414468055 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3085019010432118828936111) ^ 1028339670144039609645370 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3085019010432118828936111) ^ 617003802086423765787222 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3085019010432118828936111) ^ 134428154669777370 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3085019010432118828936111) ^ 688476090 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_4306014865996475488586537 : Nat.Prime 4306014865996475488586537 := by
  apply lucas_primality 4306014865996475488586537 (3 : ZMod 4306014865996475488586537)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (233, 1), (263, 1), (1040489, 1), (272316954397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (233, 1), (263, 1), (1040489, 1), (272316954397, 1)] : List FactorBlock).map factorBlockValue).prod) = 4306014865996475488586537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_31
      · exact prime_oneHundredSixtyTwoFD_233
      · exact prime_oneHundredSixtyTwoFD_263
      · exact prime_oneHundredSixtyTwoFD_1040489
      · exact prime_oneHundredSixtyTwoFD_272316954397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4306014865996475488586537) ^ 2153007432998237744293268 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4306014865996475488586537) ^ 138903705354725015760856 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4306014865996475488586537) ^ 18480750497838950594792 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4306014865996475488586537) ^ 16372680098845914405272 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4306014865996475488586537) ^ 4138453040826453224 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4306014865996475488586537) ^ 15812511106888 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_7650073303429351064740397 : Nat.Prime 7650073303429351064740397 := by
  apply lucas_primality 7650073303429351064740397 (2 : ZMod 7650073303429351064740397)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11388258337, 1), (167937736330027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11388258337, 1), (167937736330027, 1)] : List FactorBlock).map factorBlockValue).prod) = 7650073303429351064740397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_11388258337
      · exact prime_oneHundredSixtyTwoFD_167937736330027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7650073303429351064740397) ^ 3825036651714675532370198 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7650073303429351064740397) ^ 671750945320108 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7650073303429351064740397) ^ 45553033348 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_9866943239640267541952531 : Nat.Prime 9866943239640267541952531 := by
  apply lucas_primality 9866943239640267541952531 (6 : ZMod 9866943239640267541952531)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (986694323964026754195253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (986694323964026754195253, 1)] : List FactorBlock).map factorBlockValue).prod) = 9866943239640267541952531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_986694323964026754195253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 9866943239640267541952531) ^ 4933471619820133770976265 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 9866943239640267541952531) ^ 1973388647928053508390506 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 9866943239640267541952531) ^ 10 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_15580186709888329395333977 : Nat.Prime 15580186709888329395333977 := by
  apply lucas_primality 15580186709888329395333977 (3 : ZMod 15580186709888329395333977)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (499, 1), (2053, 1), (1901048408298370901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (499, 1), (2053, 1), (1901048408298370901, 1)] : List FactorBlock).map factorBlockValue).prod) = 15580186709888329395333977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_499
      · exact prime_oneHundredSixtyTwoFD_2053
      · exact prime_oneHundredSixtyTwoFD_1901048408298370901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 15580186709888329395333977) ^ 7790093354944164697666988 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 15580186709888329395333977) ^ 31222819057892443678024 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 15580186709888329395333977) ^ 7588985245927096636792 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 15580186709888329395333977) ^ 8195576 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_16904433823888546624610819 : Nat.Prime 16904433823888546624610819 := by
  apply lucas_primality 16904433823888546624610819 (2 : ZMod 16904433823888546624610819)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (29, 1), (71, 1), (2551, 1), (1379867, 1), (89706362731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (29, 1), (71, 1), (2551, 1), (1379867, 1), (89706362731, 1)] : List FactorBlock).map factorBlockValue).prod) = 16904433823888546624610819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_29
      · exact prime_oneHundredSixtyTwoFD_71
      · exact prime_oneHundredSixtyTwoFD_2551
      · exact prime_oneHundredSixtyTwoFD_1379867
      · exact prime_oneHundredSixtyTwoFD_89706362731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16904433823888546624610819) ^ 8452216911944273312305409 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16904433823888546624610819) ^ 1300341063376042048046986 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16904433823888546624610819) ^ 582911511168570573262442 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16904433823888546624610819) ^ 238090617237866853867758 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16904433823888546624610819) ^ 6626591071692883819918 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16904433823888546624610819) ^ 12250770417647894054 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16904433823888546624610819) ^ 188441859743878 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_68062272645578263417498429 : Nat.Prime 68062272645578263417498429 := by
  apply lucas_primality 68062272645578263417498429 (2 : ZMod 68062272645578263417498429)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (701, 1), (141948996516209640817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (701, 1), (141948996516209640817, 1)] : List FactorBlock).map factorBlockValue).prod) = 68062272645578263417498429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_19
      · exact prime_oneHundredSixtyTwoFD_701
      · exact prime_oneHundredSixtyTwoFD_141948996516209640817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68062272645578263417498429) ^ 34031136322789131708749214 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 68062272645578263417498429) ^ 22687424215192754472499476 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 68062272645578263417498429) ^ 3582224876083066495657812 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 68062272645578263417498429) ^ 97093113617087394318828 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 68062272645578263417498429) ^ 479484 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_87018280429194563042635429 : Nat.Prime 87018280429194563042635429 := by
  apply lucas_primality 87018280429194563042635429 (6 : ZMod 87018280429194563042635429)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (73, 1), (792690473, 1), (125314911616211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (73, 1), (792690473, 1), (125314911616211, 1)] : List FactorBlock).map factorBlockValue).prod) = 87018280429194563042635429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_73
      · exact prime_oneHundredSixtyTwoFD_792690473
      · exact prime_oneHundredSixtyTwoFD_125314911616211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 87018280429194563042635429) ^ 43509140214597281521317714 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 87018280429194563042635429) ^ 29006093476398187680878476 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 87018280429194563042635429) ^ 1192031238756089904693636 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 87018280429194563042635429) ^ 109775862575800836 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 87018280429194563042635429) ^ 694396854348 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_104147490606121388394149309 : Nat.Prime 104147490606121388394149309 := by
  apply lucas_primality 104147490606121388394149309 (2 : ZMod 104147490606121388394149309)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (640933, 1), (5828189, 1), (118138253869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (640933, 1), (5828189, 1), (118138253869, 1)] : List FactorBlock).map factorBlockValue).prod) = 104147490606121388394149309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_59
      · exact prime_oneHundredSixtyTwoFD_640933
      · exact prime_oneHundredSixtyTwoFD_5828189
      · exact prime_oneHundredSixtyTwoFD_118138253869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 104147490606121388394149309) ^ 52073745303060694197074654 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 104147490606121388394149309) ^ 1765211705188498108375412 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 104147490606121388394149309) ^ 162493568916129124876 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 104147490606121388394149309) ^ 17869614490216667372 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 104147490606121388394149309) ^ 881572963839532 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_509380944746428811853299413 : Nat.Prime 509380944746428811853299413 := by
  apply lucas_primality 509380944746428811853299413 (6 : ZMod 509380944746428811853299413)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (13, 1), (17, 1), (14779, 1), (618877695587683109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (13, 1), (17, 1), (14779, 1), (618877695587683109, 1)] : List FactorBlock).map factorBlockValue).prod) = 509380944746428811853299413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_14779
      · exact prime_oneHundredSixtyTwoFD_618877695587683109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 509380944746428811853299413) ^ 254690472373214405926649706 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 509380944746428811853299413) ^ 169793648248809603951099804 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 509380944746428811853299413) ^ 72768706392346973121899916 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 509380944746428811853299413) ^ 39183149595879139373330724 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 509380944746428811853299413) ^ 29963584985084047756076436 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 509380944746428811853299413) ^ 34466536622669247706428 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 509380944746428811853299413) ^ 823072068 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_613869343668773183515514677 : Nat.Prime 613869343668773183515514677 := by
  apply lucas_primality 613869343668773183515514677 (6 : ZMod 613869343668773183515514677)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (47, 1), (14779, 1), (618877695587683109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (47, 1), (14779, 1), (618877695587683109, 1)] : List FactorBlock).map factorBlockValue).prod) = 613869343668773183515514677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_47
      · exact prime_oneHundredSixtyTwoFD_14779
      · exact prime_oneHundredSixtyTwoFD_618877695587683109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 613869343668773183515514677) ^ 306934671834386591757757338 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 204623114556257727838504892 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 87695620524110454787930668 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 36109961392280775500912628 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 13061049865293046457776908 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 41536595417062939543644 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 991907364 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_878565299195675381912112749 : Nat.Prime 878565299195675381912112749 := by
  apply lucas_primality 878565299195675381912112749 (2 : ZMod 878565299195675381912112749)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (103, 1), (293, 1), (117048473, 1), (1053880686179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (103, 1), (293, 1), (117048473, 1), (1053880686179, 1)] : List FactorBlock).map factorBlockValue).prod) = 878565299195675381912112749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_59
      · exact prime_oneHundredSixtyTwoFD_103
      · exact prime_oneHundredSixtyTwoFD_293
      · exact prime_oneHundredSixtyTwoFD_117048473
      · exact prime_oneHundredSixtyTwoFD_1053880686179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 878565299195675381912112749) ^ 439282649597837690956056374 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 878565299195675381912112749) ^ 14890937274502972574781572 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 878565299195675381912112749) ^ 8529760186365780406913716 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 878565299195675381912112749) ^ 2998516379507424511645436 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 878565299195675381912112749) ^ 7505995393854265676 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 878565299195675381912112749) ^ 833647784533412 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_1339351295277323309488395659 : Nat.Prime 1339351295277323309488395659 := by
  apply lucas_primality 1339351295277323309488395659 (2 : ZMod 1339351295277323309488395659)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (74383, 1), (109891, 1), (1063991027156509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (74383, 1), (109891, 1), (1063991027156509, 1)] : List FactorBlock).map factorBlockValue).prod) = 1339351295277323309488395659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_11
      · exact prime_oneHundredSixtyTwoFD_74383
      · exact prime_oneHundredSixtyTwoFD_109891
      · exact prime_oneHundredSixtyTwoFD_1063991027156509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1339351295277323309488395659) ^ 669675647638661654744197829 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1339351295277323309488395659) ^ 191335899325331901355485094 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1339351295277323309488395659) ^ 121759208661574846317126878 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1339351295277323309488395659) ^ 18006147846649413299926 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1339351295277323309488395659) ^ 12187998064239321777838 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1339351295277323309488395659) ^ 1258799426962 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_6384241174155241108561352641 : Nat.Prime 6384241174155241108561352641 := by
  apply lucas_primality 6384241174155241108561352641 (7 : ZMod 6384241174155241108561352641)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 6384241174155241108561352641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_171401
      · exact prime_oneHundredSixtyTwoFD_714027719
      · exact prime_oneHundredSixtyTwoFD_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6384241174155241108561352641) ^ 3192120587077620554280676320 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 6384241174155241108561352641) ^ 2128080391385080369520450880 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 6384241174155241108561352641) ^ 1276848234831048221712270528 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 6384241174155241108561352641) ^ 37247397472332373256640 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 6384241174155241108561352641) ^ 8941167134374570560 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (7 : ZMod 6384241174155241108561352641) ^ 1057406962155716160 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_15960602935388102771403381607 : Nat.Prime 15960602935388102771403381607 := by
  apply lucas_primality 15960602935388102771403381607 (3 : ZMod 15960602935388102771403381607)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2411, 1), (7039, 1), (188911, 1), (829722028640579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2411, 1), (7039, 1), (188911, 1), (829722028640579, 1)] : List FactorBlock).map factorBlockValue).prod) = 15960602935388102771403381607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_2411
      · exact prime_oneHundredSixtyTwoFD_7039
      · exact prime_oneHundredSixtyTwoFD_188911
      · exact prime_oneHundredSixtyTwoFD_829722028640579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15960602935388102771403381607) ^ 7980301467694051385701690803 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 15960602935388102771403381607) ^ 5320200978462700923801127202 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 15960602935388102771403381607) ^ 6619909969053547395853746 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 15960602935388102771403381607) ^ 2267453180194360388038554 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 15960602935388102771403381607) ^ 84487419659988580714746 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 15960602935388102771403381607) ^ 19236084356514 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_21280803913850803695204508801 : Nat.Prime 21280803913850803695204508801 := by
  apply lucas_primality 21280803913850803695204508801 (14 : ZMod 21280803913850803695204508801)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850803695204508801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_5
      · exact prime_oneHundredSixtyTwoFD_171401
      · exact prime_oneHundredSixtyTwoFD_714027719
      · exact prime_oneHundredSixtyTwoFD_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 21280803913850803695204508801) ^ 10640401956925401847602254400 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 7093601304616934565068169600 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 4256160782770160739040901760 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 124157991574441244188800 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 29803890447915235200 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 3524689873852387200 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_23940904403082154157105072407 : Nat.Prime 23940904403082154157105072407 := by
  apply lucas_primality 23940904403082154157105072407 (3 : ZMod 23940904403082154157105072407)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (388373, 1), (133428789850506403081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (388373, 1), (133428789850506403081, 1)] : List FactorBlock).map factorBlockValue).prod) = 23940904403082154157105072407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_11
      · exact prime_oneHundredSixtyTwoFD_388373
      · exact prime_oneHundredSixtyTwoFD_133428789850506403081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23940904403082154157105072407) ^ 11970452201541077078552536203 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 23940904403082154157105072407) ^ 7980301467694051385701690802 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 23940904403082154157105072407) ^ 3420129200440307736729296058 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 23940904403082154157105072407) ^ 2176445854825650377918642946 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 23940904403082154157105072407) ^ 61644100910933958223422 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 23940904403082154157105072407) ^ 179428326 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_47881808806164308314210144807 : Nat.Prime 47881808806164308314210144807 := by
  apply lucas_primality 47881808806164308314210144807 (3 : ZMod 47881808806164308314210144807)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (613869343668773183515514677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (613869343668773183515514677, 1)] : List FactorBlock).map factorBlockValue).prod) = 47881808806164308314210144807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_613869343668773183515514677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 47881808806164308314210144807) ^ 23940904403082154157105072403 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 47881808806164308314210144807) ^ 15960602935388102771403381602 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 47881808806164308314210144807) ^ 3683216062012639101093088062 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (3 : ZMod 47881808806164308314210144807) ^ 78 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_63842411741552411085613526413 : Nat.Prime 63842411741552411085613526413 := by
  apply lucas_primality 63842411741552411085613526413 (5 : ZMod 63842411741552411085613526413)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3662228970263, 1), (1452722104942727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3662228970263, 1), (1452722104942727, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552411085613526413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_3662228970263
      · exact prime_oneHundredSixtyTwoFD_1452722104942727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 63842411741552411085613526413) ^ 31921205870776205542806763206 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 63842411741552411085613526413) ^ 21280803913850803695204508804 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 63842411741552411085613526413) ^ 17432665259312724 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (5 : ZMod 63842411741552411085613526413) ^ 43946747643156 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_191527235224657233256840579219 : Nat.Prime 191527235224657233256840579219 := by
  apply lucas_primality 191527235224657233256840579219 (2 : ZMod 191527235224657233256840579219)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (73, 1), (83, 1), (906208483, 1), (113993486613649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (73, 1), (83, 1), (906208483, 1), (113993486613649, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_17
      · exact prime_oneHundredSixtyTwoFD_73
      · exact prime_oneHundredSixtyTwoFD_83
      · exact prime_oneHundredSixtyTwoFD_906208483
      · exact prime_oneHundredSixtyTwoFD_113993486613649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 191527235224657233256840579219) ^ 95763617612328616628420289609 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579219) ^ 63842411741552411085613526406 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579219) ^ 11266307954391601956284739954 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579219) ^ 2623660756502153880230692866 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579219) ^ 2307557050899484738034223846 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579219) ^ 211350079829982383046 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579219) ^ 1680159462740082 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_191527235224657233256840579267 : Nat.Prime 191527235224657233256840579267 := by
  apply lucas_primality 191527235224657233256840579267 (2 : ZMod 191527235224657233256840579267)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1602869, 1), (32246411, 1), (26851715585323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1602869, 1), (32246411, 1), (26851715585323, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_3
      · exact prime_oneHundredSixtyTwoFD_23
      · exact prime_oneHundredSixtyTwoFD_1602869
      · exact prime_oneHundredSixtyTwoFD_32246411
      · exact prime_oneHundredSixtyTwoFD_26851715585323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 191527235224657233256840579267) ^ 95763617612328616628420289633 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579267) ^ 63842411741552411085613526422 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579267) ^ 8327271096724227532906112142 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579267) ^ 119490261041081481553914 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579267) ^ 5939489986177290652806 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579267) ^ 7132774612335942 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyTwoFD_191527235224657233256840579277 : Nat.Prime 191527235224657233256840579277 := by
  apply lucas_primality 191527235224657233256840579277 (2 : ZMod 191527235224657233256840579277)
  · rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (199, 1), (2819, 1), (4561, 1), (111103, 1), (1850951952683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (199, 1), (2819, 1), (4561, 1), (111103, 1), (1850951952683, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyTwoFD_2
      · exact prime_oneHundredSixtyTwoFD_7
      · exact prime_oneHundredSixtyTwoFD_13
      · exact prime_oneHundredSixtyTwoFD_199
      · exact prime_oneHundredSixtyTwoFD_2819
      · exact prime_oneHundredSixtyTwoFD_4561
      · exact prime_oneHundredSixtyTwoFD_111103
      · exact prime_oneHundredSixtyTwoFD_1850951952683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 191527235224657233256840579277) ^ 95763617612328616628420289638 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579277) ^ 27361033603522461893834368468 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579277) ^ 14732864248050556404372352252 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579277) ^ 962448418214357956064525524 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579277) ^ 67941552048477202290472004 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579277) ^ 41992377817289461358658316 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579277) ^ 1723870959601966042832692 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide
    · change (2 : ZMod 191527235224657233256840579277) ^ 103474990232476772 ≠ 1
      rw [← oneHundredSixtyTwoFDFastPow_eq_pow]
      decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579200 : Nat.totient 191527235224657233256840579200 = 51073631334074024124291072000 := by
  rw [← show ((([(2, 7), (3, 4), (5, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_171401, prime_oneHundredSixtyTwoFD_714027719, prime_oneHundredSixtyTwoFD_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579201 : Nat.totient 191527235224657233256840579201 = 180251902037698285651905613824 := by
  rw [← show ((([(17, 1), (19973, 1), (85204051633, 1), (6620306085517, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_17, prime_oneHundredSixtyTwoFD_19973, prime_oneHundredSixtyTwoFD_85204051633, prime_oneHundredSixtyTwoFD_6620306085517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579202 : Nat.totient 191527235224657233256840579202 = 95763617611873077031273800900 := by
  rw [← show ((([(2, 1), (210220280311, 1), (455539386926208391, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_210220280311, prime_oneHundredSixtyTwoFD_455539386926208391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579203 : Nat.totient 191527235224657233256840579203 = 127489851531330352770117877920 := by
  rw [← show ((([(3, 1), (967, 1), (2027, 1), (44618071, 1), (729992287516259, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_967, prime_oneHundredSixtyTwoFD_2027, prime_oneHundredSixtyTwoFD_44618071, prime_oneHundredSixtyTwoFD_729992287516259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579204 : Nat.totient 191527235224657233256840579204 = 82345679084758058101409840640 := by
  rw [← show ((([(2, 2), (11, 1), (19, 1), (827, 1), (2707, 1), (20054149, 1), (5103008119549, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_11, prime_oneHundredSixtyTwoFD_19, prime_oneHundredSixtyTwoFD_827, prime_oneHundredSixtyTwoFD_2707, prime_oneHundredSixtyTwoFD_20054149, prime_oneHundredSixtyTwoFD_5103008119549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579205 : Nat.totient 191527235224657233256840579205 = 153221625809619474900569229888 := by
  rw [← show ((([(5, 1), (952583, 1), (100714093, 1), (399270719554739, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_952583, prime_oneHundredSixtyTwoFD_100714093, prime_oneHundredSixtyTwoFD_399270719554739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579206 : Nat.totient 191527235224657233256840579206 = 53905319935297984626658754976 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (67, 1), (68062272645578263417498429, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_7, prime_oneHundredSixtyTwoFD_67, prime_oneHundredSixtyTwoFD_68062272645578263417498429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579207 : Nat.totient 191527235224657233256840579207 = 187947819565327593703608768000 := by
  rw [← show ((([(61, 1), (431, 1), (74257, 1), (98103846261021787661, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_61, prime_oneHundredSixtyTwoFD_431, prime_oneHundredSixtyTwoFD_74257, prime_oneHundredSixtyTwoFD_98103846261021787661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579208 : Nat.totient 191527235224657233256840579208 = 95763617209800054236712609216 := by
  rw [← show ((([(2, 3), (237905149, 1), (100632140597689014949, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_237905149, prime_oneHundredSixtyTwoFD_100632140597689014949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579209 : Nat.totient 191527235224657233256840579209 = 127684823483104822171227052800 := by
  rw [← show ((([(3, 2), (21280803913850803695204508801, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_21280803913850803695204508801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579210 : Nat.totient 191527235224657233256840579210 = 76610894089837834697857543168 := by
  rw [← show ((([(2, 1), (5, 1), (3058762392017, 1), (6261592457280113, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_3058762392017, prime_oneHundredSixtyTwoFD_6261592457280113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579211 : Nat.totient 191527235224657233256840579211 = 176726499061700727031568332800 := by
  rw [← show ((([(13, 1), (2939, 1), (22901, 1), (218893645606608292673, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_13, prime_oneHundredSixtyTwoFD_2939, prime_oneHundredSixtyTwoFD_22901, prime_oneHundredSixtyTwoFD_218893645606608292673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579212 : Nat.totient 191527235224657233256840579212 = 63140848857911274824701209600 := by
  rw [← show ((([(2, 2), (3, 1), (173, 1), (191, 1), (300331, 1), (1608309624659490097, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_173, prime_oneHundredSixtyTwoFD_191, prime_oneHundredSixtyTwoFD_300331, prime_oneHundredSixtyTwoFD_1608309624659490097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579213 : Nat.totient 191527235224657233256840579213 = 163259206032067728427298941200 := by
  rw [← show ((([(7, 3), (181, 1), (3085019010432118828936111, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_7, prime_oneHundredSixtyTwoFD_181, prime_oneHundredSixtyTwoFD_3085019010432118828936111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579214 : Nat.totient 191527235224657233256840579214 = 95763535680380545687908546936 := by
  rw [← show ((([(2, 1), (1168819, 1), (81931948070940510573853, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_1168819, prime_oneHundredSixtyTwoFD_81931948070940510573853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579215 : Nat.totient 191527235224657233256840579215 = 92438395676600886437031936000 := by
  rw [← show ((([(3, 1), (5, 1), (11, 2), (241, 1), (2441, 1), (1012597, 1), (177146449272173, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_11, prime_oneHundredSixtyTwoFD_241, prime_oneHundredSixtyTwoFD_2441, prime_oneHundredSixtyTwoFD_1012597, prime_oneHundredSixtyTwoFD_177146449272173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579216 : Nat.totient 191527235224657233256840579216 = 95703758582657636610836582400 := by
  rw [← show ((([(2, 4), (1657, 1), (49531, 1), (717331, 1), (203325267622513, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_1657, prime_oneHundredSixtyTwoFD_49531, prime_oneHundredSixtyTwoFD_717331, prime_oneHundredSixtyTwoFD_203325267622513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579217 : Nat.totient 191527235224657233256840579217 = 184759721703475456235109759360 := by
  rw [← show ((([(37, 1), (131, 1), (1097, 1), (36020595815294828169863, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_37, prime_oneHundredSixtyTwoFD_131, prime_oneHundredSixtyTwoFD_1097, prime_oneHundredSixtyTwoFD_36020595815294828169863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579218 : Nat.totient 191527235224657233256840579218 = 58549843947253601761539047424 := by
  rw [← show ((([(2, 1), (3, 2), (17, 1), (73, 1), (83, 1), (906208483, 1), (113993486613649, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_17, prime_oneHundredSixtyTwoFD_73, prime_oneHundredSixtyTwoFD_83, prime_oneHundredSixtyTwoFD_906208483, prime_oneHundredSixtyTwoFD_113993486613649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579219 : Nat.totient 191527235224657233256840579219 = 191527235224657233256840579218 := by
  rw [← show ((([(191527235224657233256840579219, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_191527235224657233256840579219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579220 : Nat.totient 191527235224657233256840579220 = 62164504957349241541192462848 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (23, 1), (107, 1), (1039, 1), (535026560709385213837, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_7, prime_oneHundredSixtyTwoFD_23, prime_oneHundredSixtyTwoFD_107, prime_oneHundredSixtyTwoFD_1039, prime_oneHundredSixtyTwoFD_535026560709385213837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579221 : Nat.totient 191527235224657233256840579221 = 123281891622624066220182094080 := by
  rw [← show ((([(3, 1), (29, 1), (17833891, 1), (123442633682500070513, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_29, prime_oneHundredSixtyTwoFD_17833891, prime_oneHundredSixtyTwoFD_123442633682500070513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579222 : Nat.totient 191527235224657233256840579222 = 93956756655385646726399681440 := by
  rw [← show ((([(2, 1), (53, 1), (379966547, 1), (4755315234808230821, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_53, prime_oneHundredSixtyTwoFD_379966547, prime_oneHundredSixtyTwoFD_4755315234808230821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579223 : Nat.totient 191527235224657233256840579223 = 181369346155771547579264896320 := by
  rw [← show ((([(19, 1), (2341, 1), (4306014865996475488586537, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_19, prime_oneHundredSixtyTwoFD_2341, prime_oneHundredSixtyTwoFD_4306014865996475488586537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579224 : Nat.totient 191527235224657233256840579224 = 58931456992202225617489408896 := by
  rw [← show ((([(2, 3), (3, 1), (13, 1), (613869343668773183515514677, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_13, prime_oneHundredSixtyTwoFD_613869343668773183515514677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579225 : Nat.totient 191527235224657233256840579225 = 149330731892573262591608832000 := by
  rw [← show ((([(5, 2), (43, 1), (457, 1), (648289, 1), (3094661, 1), (194322970511, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_43, prime_oneHundredSixtyTwoFD_457, prime_oneHundredSixtyTwoFD_648289, prime_oneHundredSixtyTwoFD_3094661, prime_oneHundredSixtyTwoFD_194322970511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579226 : Nat.totient 191527235224657233256840579226 = 86719058765005392633360752640 := by
  rw [← show ((([(2, 1), (11, 1), (257, 1), (2991193, 1), (11324793704342693983, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_11, prime_oneHundredSixtyTwoFD_257, prime_oneHundredSixtyTwoFD_2991193, prime_oneHundredSixtyTwoFD_11324793704342693983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579227 : Nat.totient 191527235224657233256840579227 = 109349213222056812148125434880 := by
  rw [← show ((([(3, 3), (7, 1), (1153, 1), (878899926231809511221431, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_7, prime_oneHundredSixtyTwoFD_1153, prime_oneHundredSixtyTwoFD_878899926231809511221431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579228 : Nat.totient 191527235224657233256840579228 = 95763617612328616628420289612 := by
  rw [← show ((([(2, 2), (47881808806164308314210144807, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_47881808806164308314210144807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579229 : Nat.totient 191527235224657233256840579229 = 182738388901308582389534398800 := by
  rw [← show ((([(31, 1), (71, 1), (87018280429194563042635429, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_31, prime_oneHundredSixtyTwoFD_71, prime_oneHundredSixtyTwoFD_87018280429194563042635429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579230 : Nat.totient 191527235224657233256840579230 = 51073929393241928868490821120 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (6384241174155241108561352641, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_6384241174155241108561352641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579231 : Nat.totient 191527235224657233256840579231 = 191298259081541701491573050880 := by
  rw [← show ((([(911, 1), (10289, 1), (1854943, 1), (4764629, 1), (2311954787, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_911, prime_oneHundredSixtyTwoFD_10289, prime_oneHundredSixtyTwoFD_1854943, prime_oneHundredSixtyTwoFD_4764629, prime_oneHundredSixtyTwoFD_2311954787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579232 : Nat.totient 191527235224657233256840579232 = 93427915770543736218269306880 := by
  rw [← show ((([(2, 5), (41, 1), (24259177, 1), (6017562937482896693, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_41, prime_oneHundredSixtyTwoFD_24259177, prime_oneHundredSixtyTwoFD_6017562937482896693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579233 : Nat.totient 191527235224657233256840579233 = 127684823442746080132054162224 := by
  rw [← show ((([(3, 1), (3163746367, 1), (20179371016422698933, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_3163746367, prime_oneHundredSixtyTwoFD_20179371016422698933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579234 : Nat.totient 191527235224657233256840579234 = 82083023713290932942257816128 := by
  rw [← show ((([(2, 1), (7, 1), (1068589, 1), (290249437, 1), (44108310034367, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_7, prime_oneHundredSixtyTwoFD_1068589, prime_oneHundredSixtyTwoFD_290249437, prime_oneHundredSixtyTwoFD_44108310034367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579235 : Nat.totient 191527235224657233256840579235 = 144129535247598091588652236800 := by
  rw [← show ((([(5, 1), (17, 1), (1847, 1), (127681, 1), (322725521, 1), (29606367953, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_17, prime_oneHundredSixtyTwoFD_1847, prime_oneHundredSixtyTwoFD_127681, prime_oneHundredSixtyTwoFD_322725521, prime_oneHundredSixtyTwoFD_29606367953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579236 : Nat.totient 191527235224657233256840579236 = 63842411741534934473606570544 := by
  rw [← show ((([(2, 2), (3, 2), (3662228970263, 1), (1452722104942727, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_3662228970263, prime_oneHundredSixtyTwoFD_1452722104942727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579237 : Nat.totient 191527235224657233256840579237 = 160722155433278797138607478960 := by
  rw [← show ((([(11, 1), (13, 1), (1339351295277323309488395659, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_11, prime_oneHundredSixtyTwoFD_13, prime_oneHundredSixtyTwoFD_1339351295277323309488395659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579238 : Nat.totient 191527235224657233256840579238 = 95762830010491843808259936000 := by
  rw [← show ((([(2, 1), (122251, 1), (22449137, 1), (34893816528424937, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_122251, prime_oneHundredSixtyTwoFD_22449137, prime_oneHundredSixtyTwoFD_34893816528424937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579239 : Nat.totient 191527235224657233256840579239 = 127684823483104822171227052824 := by
  rw [← show ((([(3, 1), (63842411741552411085613526413, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_63842411741552411085613526413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579240 : Nat.totient 191527235224657233256840579240 = 76559580543070685116685126400 := by
  rw [← show ((([(2, 3), (5, 1), (1493, 1), (494240567, 1), (6488918974239451, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_1493, prime_oneHundredSixtyTwoFD_494240567, prime_oneHundredSixtyTwoFD_6488918974239451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579241 : Nat.totient 191527235224657233256840579241 = 157950027380161402811576100240 := by
  rw [← show ((([(7, 1), (47, 1), (59, 1), (9866943239640267541952531, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_7, prime_oneHundredSixtyTwoFD_47, prime_oneHundredSixtyTwoFD_59, prime_oneHundredSixtyTwoFD_9866943239640267541952531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579242 : Nat.totient 191527235224657233256840579242 = 60210778751255119943012068800 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (223, 1), (211231, 1), (35666719808417469181, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_19, prime_oneHundredSixtyTwoFD_223, prime_oneHundredSixtyTwoFD_211231, prime_oneHundredSixtyTwoFD_35666719808417469181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579243 : Nat.totient 191527235224657233256840579243 = 183134862173497301837494032000 := by
  rw [← show ((([(23, 1), (5171, 1), (6173, 1), (106008151, 1), (2460892423277, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_23, prime_oneHundredSixtyTwoFD_5171, prime_oneHundredSixtyTwoFD_6173, prime_oneHundredSixtyTwoFD_106008151, prime_oneHundredSixtyTwoFD_2460892423277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579244 : Nat.totient 191527235224657233256840579244 = 94774257072475841056027723776 := by
  rw [← show ((([(2, 2), (97, 1), (44987, 1), (10972656432056158334449, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_97, prime_oneHundredSixtyTwoFD_44987, prime_oneHundredSixtyTwoFD_10972656432056158334449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579245 : Nat.totient 191527235224657233256840579245 = 102146648346037988205906408576 := by
  rw [← show ((([(3, 2), (5, 1), (84389, 1), (50435018577897128050349, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_84389, prime_oneHundredSixtyTwoFD_50435018577897128050349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579246 : Nat.totient 191527235224657233256840579246 = 95763616471917689875847215936 := by
  rw [← show ((([(2, 1), (84395117, 1), (31009114457, 1), (36592649867, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_84395117, prime_oneHundredSixtyTwoFD_31009114457, prime_oneHundredSixtyTwoFD_36592649867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579247 : Nat.totient 191527235224657233256840579247 = 190705229901426062539700219520 := by
  rw [← show ((([(233, 1), (8732808121, 1), (94128405205272079, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_233, prime_oneHundredSixtyTwoFD_8732808121, prime_oneHundredSixtyTwoFD_94128405205272079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579248 : Nat.totient 191527235224657233256840579248 = 49747205732948037865906329600 := by
  rw [← show ((([(2, 4), (3, 1), (7, 1), (11, 1), (388373, 1), (133428789850506403081, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_7, prime_oneHundredSixtyTwoFD_11, prime_oneHundredSixtyTwoFD_388373, prime_oneHundredSixtyTwoFD_133428789850506403081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579249 : Nat.totient 191527235224657233256840579249 = 191527235224656356358436953636 := by
  rw [← show ((([(411794608482007, 1), (465103795143607, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_411794608482007, prime_oneHundredSixtyTwoFD_465103795143607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579250 : Nat.totient 191527235224657233256840579250 = 68279205342689475198194592000 := by
  rw [← show ((([(2, 1), (5, 3), (13, 1), (29, 1), (2032119206627662952327221, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_13, prime_oneHundredSixtyTwoFD_29, prime_oneHundredSixtyTwoFD_2032119206627662952327221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579251 : Nat.totient 191527235224657233256840579251 = 127476528501892579394438752992 := by
  rw [← show ((([(3, 1), (613, 1), (104147490606121388394149309, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_613, prime_oneHundredSixtyTwoFD_104147490606121388394149309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579252 : Nat.totient 191527235224657233256840579252 = 90073142968516075158188851200 := by
  rw [← show ((([(2, 2), (17, 1), (1637, 1), (39821, 1), (263185981, 1), (164171600897, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_17, prime_oneHundredSixtyTwoFD_1637, prime_oneHundredSixtyTwoFD_39821, prime_oneHundredSixtyTwoFD_263185981, prime_oneHundredSixtyTwoFD_164171600897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579253 : Nat.totient 191527235224657233256840579253 = 191499362084023331773257504000 := by
  rw [← show ((([(7481, 1), (84313, 1), (303652137242507412901, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_7481, prime_oneHundredSixtyTwoFD_84313, prime_oneHundredSixtyTwoFD_303652137242507412901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579254 : Nat.totient 191527235224657233256840579254 = 62114948757588075450769615104 := by
  rw [← show ((([(2, 1), (3, 3), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_37, prime_oneHundredSixtyTwoFD_31177, prime_oneHundredSixtyTwoFD_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579255 : Nat.totient 191527235224657233256840579255 = 131330685517370883374395848192 := by
  rw [← show ((([(5, 1), (7, 1), (57709, 1), (94824147372238166988977, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_7, prime_oneHundredSixtyTwoFD_57709, prime_oneHundredSixtyTwoFD_94824147372238166988977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579256 : Nat.totient 191527235224657233256840579256 = 95763617612328616628420289624 := by
  rw [← show ((([(2, 3), (23940904403082154157105072407, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_23940904403082154157105072407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579257 : Nat.totient 191527235224657233256840579257 = 126204769095300330734002878720 := by
  rw [← show ((([(3, 1), (139, 1), (229, 1), (19813, 1), (82811, 1), (1222420807213043, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_139, prime_oneHundredSixtyTwoFD_229, prime_oneHundredSixtyTwoFD_19813, prime_oneHundredSixtyTwoFD_82811, prime_oneHundredSixtyTwoFD_1222420807213043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579258 : Nat.totient 191527235224657233256840579258 = 95289573804633097105992375600 := by
  rw [← show ((([(2, 1), (211, 1), (4723, 1), (12092323, 1), (7946765611782791, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_211, prime_oneHundredSixtyTwoFD_4723, prime_oneHundredSixtyTwoFD_12092323, prime_oneHundredSixtyTwoFD_7946765611782791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579259 : Nat.totient 191527235224657233256840579259 = 174115123011705853455291752200 := by
  rw [← show ((([(11, 1), (319259, 1), (54537434617677819649091, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_11, prime_oneHundredSixtyTwoFD_319259, prime_oneHundredSixtyTwoFD_54537434617677819649091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579260 : Nat.totient 191527235224657233256840579260 = 48790356351122334789453000960 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (31, 1), (79, 1), (4703, 1), (277150409895147902543, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_31, prime_oneHundredSixtyTwoFD_79, prime_oneHundredSixtyTwoFD_4703, prime_oneHundredSixtyTwoFD_277150409895147902543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579261 : Nat.totient 191527235224657233256840579261 = 181166411062581494208943472928 := by
  rw [← show ((([(19, 1), (647, 1), (15580186709888329395333977, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_19, prime_oneHundredSixtyTwoFD_647, prime_oneHundredSixtyTwoFD_15580186709888329395333977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579262 : Nat.totient 191527235224657233256840579262 = 81579523501424233121582898432 := by
  rw [← show ((([(2, 1), (7, 2), (163, 1), (22936899989, 1), (522735672782417, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_7, prime_oneHundredSixtyTwoFD_163, prime_oneHundredSixtyTwoFD_22936899989, prime_oneHundredSixtyTwoFD_522735672782417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579263 : Nat.totient 191527235224657233256840579263 = 117862913984392956763664512128 := by
  rw [← show ((([(3, 2), (13, 1), (11013696930283, 1), (148631737990633, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_13, prime_oneHundredSixtyTwoFD_11013696930283, prime_oneHundredSixtyTwoFD_148631737990633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579264 : Nat.totient 191527235224657233256840579264 = 95689716017347937783444520960 := by
  rw [← show ((([(2, 6), (1297, 1), (1430641, 1), (1612797799865644963, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_1297, prime_oneHundredSixtyTwoFD_1430641, prime_oneHundredSixtyTwoFD_1612797799865644963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579265 : Nat.totient 191527235224657233256840579265 = 152764001597601625572012360000 := by
  rw [← show ((([(5, 1), (373, 1), (3251, 1), (31588916790240203799011, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_373, prime_oneHundredSixtyTwoFD_3251, prime_oneHundredSixtyTwoFD_31588916790240203799011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579266 : Nat.totient 191527235224657233256840579266 = 61066614717215378736627771840 := by
  rw [← show ((([(2, 1), (3, 1), (23, 1), (1602869, 1), (32246411, 1), (26851715585323, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_23, prime_oneHundredSixtyTwoFD_1602869, prime_oneHundredSixtyTwoFD_32246411, prime_oneHundredSixtyTwoFD_26851715585323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579267 : Nat.totient 191527235224657233256840579267 = 191527235224657233256840579266 := by
  rw [← show ((([(191527235224657233256840579267, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_191527235224657233256840579267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579268 : Nat.totient 191527235224657233256840579268 = 91842792099831961221080678400 := by
  rw [← show ((([(2, 2), (43, 1), (61, 1), (761, 1), (4289, 1), (5087, 1), (1099435654448473, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_43, prime_oneHundredSixtyTwoFD_61, prime_oneHundredSixtyTwoFD_761, prime_oneHundredSixtyTwoFD_4289, prime_oneHundredSixtyTwoFD_5087, prime_oneHundredSixtyTwoFD_1099435654448473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579269 : Nat.totient 191527235224657233256840579269 = 102592396727252505395376537600 := by
  rw [← show ((([(3, 1), (7, 1), (17, 1), (349, 1), (907, 1), (19421, 1), (585911, 1), (148945151149, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_7, prime_oneHundredSixtyTwoFD_17, prime_oneHundredSixtyTwoFD_349, prime_oneHundredSixtyTwoFD_907, prime_oneHundredSixtyTwoFD_19421, prime_oneHundredSixtyTwoFD_585911, prime_oneHundredSixtyTwoFD_148945151149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579270 : Nat.totient 191527235224657233256840579270 = 68970090001465270228412137440 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (103, 1), (16904433823888546624610819, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_11, prime_oneHundredSixtyTwoFD_103, prime_oneHundredSixtyTwoFD_16904433823888546624610819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579271 : Nat.totient 191527235224657233256840579271 = 189547275451559411679923124000 := by
  rw [← show ((([(101, 1), (2267, 1), (89745571, 1), (9320616099943403, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_101, prime_oneHundredSixtyTwoFD_2267, prime_oneHundredSixtyTwoFD_89745571, prime_oneHundredSixtyTwoFD_9320616099943403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579272 : Nat.totient 191527235224657233256840579272 = 63806528289284581026551241600 := by
  rw [← show ((([(2, 3), (3, 2), (2411, 1), (7039, 1), (188911, 1), (829722028640579, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_2411, prime_oneHundredSixtyTwoFD_7039, prime_oneHundredSixtyTwoFD_188911, prime_oneHundredSixtyTwoFD_829722028640579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579273 : Nat.totient 191527235224657233256840579273 = 184066796858381937112133030400 := by
  rw [← show ((([(41, 1), (67, 1), (1233179, 1), (56538692335790847121, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_41, prime_oneHundredSixtyTwoFD_67, prime_oneHundredSixtyTwoFD_1233179, prime_oneHundredSixtyTwoFD_56538692335790847121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579274 : Nat.totient 191527235224657233256840579274 = 95760299649621292908094656000 := by
  rw [← show ((([(2, 1), (29501, 1), (1335853, 1), (705036473, 1), (3446621173, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_29501, prime_oneHundredSixtyTwoFD_1335853, prime_oneHundredSixtyTwoFD_705036473, prime_oneHundredSixtyTwoFD_3446621173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579275 : Nat.totient 191527235224657233256840579275 = 99620417697992165855340919680 := by
  rw [← show ((([(3, 1), (5, 2), (53, 1), (167, 1), (288520672202247931694107, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_53, prime_oneHundredSixtyTwoFD_167, prime_oneHundredSixtyTwoFD_288520672202247931694107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579276 : Nat.totient 191527235224657233256840579276 = 75344323215443447807155261440 := by
  rw [← show ((([(2, 2), (7, 1), (13, 1), (199, 1), (2819, 1), (4561, 1), (111103, 1), (1850951952683, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_7, prime_oneHundredSixtyTwoFD_13, prime_oneHundredSixtyTwoFD_199, prime_oneHundredSixtyTwoFD_2819, prime_oneHundredSixtyTwoFD_4561, prime_oneHundredSixtyTwoFD_111103, prime_oneHundredSixtyTwoFD_1850951952683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579277 : Nat.totient 191527235224657233256840579277 = 191527235224657233256840579276 := by
  rw [← show ((([(191527235224657233256840579277, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_191527235224657233256840579277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579278 : Nat.totient 191527235224657233256840579278 = 63842406970996938295724364288 := by
  rw [← show ((([(2, 1), (3, 1), (13680577, 1), (614504323, 1), (3797081613103, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_13680577, prime_oneHundredSixtyTwoFD_614504323, prime_oneHundredSixtyTwoFD_3797081613103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579279 : Nat.totient 191527235224657233256840579279 = 184922377174100225949739035936 := by
  rw [← show ((([(29, 1), (392927, 1), (16808179182239715252613, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_29, prime_oneHundredSixtyTwoFD_392927, prime_oneHundredSixtyTwoFD_16808179182239715252613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579280 : Nat.totient 191527235224657233256840579280 = 72551179308647582917623705600 := by
  rw [← show ((([(2, 4), (5, 1), (19, 1), (2741, 1), (66959, 1), (686544918352552681, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_19, prime_oneHundredSixtyTwoFD_2741, prime_oneHundredSixtyTwoFD_66959, prime_oneHundredSixtyTwoFD_686544918352552681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579281 : Nat.totient 191527235224657233256840579281 = 115823663369294590163936448000 := by
  rw [← show ((([(3, 5), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_11, prime_oneHundredSixtyTwoFD_461, prime_oneHundredSixtyTwoFD_69997, prime_oneHundredSixtyTwoFD_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579282 : Nat.totient 191527235224657233256840579282 = 94885052313132941246508176784 := by
  rw [← show ((([(2, 1), (109, 1), (878565299195675381912112749, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_109, prime_oneHundredSixtyTwoFD_878565299195675381912112749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579283 : Nat.totient 191527235224657233256840579283 = 164164906107426320895661461000 := by
  rw [← show ((([(7, 1), (126719, 1), (215918951408411223998251, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_7, prime_oneHundredSixtyTwoFD_126719, prime_oneHundredSixtyTwoFD_215918951408411223998251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579284 : Nat.totient 191527235224657233256840579284 = 63842411741552411085613526424 := by
  rw [← show ((([(2, 2), (3, 1), (15960602935388102771403381607, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_15960602935388102771403381607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579285 : Nat.totient 191527235224657233256840579285 = 153221534617554498064309940160 := by
  rw [← show ((([(5, 1), (604277, 1), (63390542822135290026541, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_604277, prime_oneHundredSixtyTwoFD_63390542822135290026541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579286 : Nat.totient 191527235224657233256840579286 = 90086547380225680743498547200 := by
  rw [← show ((([(2, 1), (17, 1), (2053, 1), (11829439, 1), (13245937, 1), (17511197201, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_17, prime_oneHundredSixtyTwoFD_2053, prime_oneHundredSixtyTwoFD_11829439, prime_oneHundredSixtyTwoFD_13245937, prime_oneHundredSixtyTwoFD_17511197201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579287 : Nat.totient 191527235224657233256840579287 = 126250141348426292168786726912 := by
  rw [← show ((([(3, 1), (89, 1), (5956133, 1), (120435602933347335617, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_89, prime_oneHundredSixtyTwoFD_5956133, prime_oneHundredSixtyTwoFD_120435602933347335617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579288 : Nat.totient 191527235224657233256840579288 = 93726093833342901381007091808 := by
  rw [← show ((([(2, 3), (47, 1), (509380944746428811853299413, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_47, prime_oneHundredSixtyTwoFD_509380944746428811853299413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579289 : Nat.totient 191527235224657233256840579289 = 169008125552169281687457726336 := by
  rw [← show ((([(13, 1), (23, 1), (1699, 1), (377021374415911057767289, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_13, prime_oneHundredSixtyTwoFD_23, prime_oneHundredSixtyTwoFD_1699, prime_oneHundredSixtyTwoFD_377021374415911057767289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579290 : Nat.totient 191527235224657233256840579290 = 43775556683897399316263852544 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (7, 1), (28403, 1), (79847, 1), (5816549, 1), (23046330287, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_7, prime_oneHundredSixtyTwoFD_28403, prime_oneHundredSixtyTwoFD_79847, prime_oneHundredSixtyTwoFD_5816549, prime_oneHundredSixtyTwoFD_23046330287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579291 : Nat.totient 191527235224657233256840579291 = 177534187741509938221121740800 := by
  rw [← show ((([(31, 1), (37, 1), (73, 1), (541, 1), (28933, 1), (146134759552611337, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_31, prime_oneHundredSixtyTwoFD_37, prime_oneHundredSixtyTwoFD_73, prime_oneHundredSixtyTwoFD_541, prime_oneHundredSixtyTwoFD_28933, prime_oneHundredSixtyTwoFD_146134759552611337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579292 : Nat.totient 191527235224657233256840579292 = 86904832726957428095450898560 := by
  rw [← show ((([(2, 2), (11, 1), (569, 1), (7650073303429351064740397, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_11, prime_oneHundredSixtyTwoFD_569, prime_oneHundredSixtyTwoFD_7650073303429351064740397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579293 : Nat.totient 191527235224657233256840579293 = 126109355666968908045252707840 := by
  rw [← show ((([(3, 1), (137, 1), (197, 1), (2712719, 1), (872002404010526741, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_137, prime_oneHundredSixtyTwoFD_197, prime_oneHundredSixtyTwoFD_2712719, prime_oneHundredSixtyTwoFD_872002404010526741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579294 : Nat.totient 191527235224657233256840579294 = 95763616042580497603540142392 := by
  rw [← show ((([(2, 1), (62021543, 1), (3758823767, 1), (410776899887, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_62021543, prime_oneHundredSixtyTwoFD_3758823767, prime_oneHundredSixtyTwoFD_410776899887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579295 : Nat.totient 191527235224657233256840579295 = 150559238580359608750442065920 := by
  rw [← show ((([(5, 1), (127, 1), (157, 1), (311, 1), (71209, 1), (4684117, 1), (18519708707, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_127, prime_oneHundredSixtyTwoFD_157, prime_oneHundredSixtyTwoFD_311, prime_oneHundredSixtyTwoFD_71209, prime_oneHundredSixtyTwoFD_4684117, prime_oneHundredSixtyTwoFD_18519708707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579296 : Nat.totient 191527235224657233256840579296 = 63419612296819311859553241600 := by
  rw [← show ((([(2, 5), (3, 1), (151, 1), (31458437, 1), (419996061740133023, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_151, prime_oneHundredSixtyTwoFD_31458437, prime_oneHundredSixtyTwoFD_419996061740133023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579297 : Nat.totient 191527235224657233256840579297 = 164165904451054342910325712320 := by
  rw [← show ((([(7, 1), (699709, 1), (2624581, 1), (14898929285702599, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_7, prime_oneHundredSixtyTwoFD_699709, prime_oneHundredSixtyTwoFD_2624581, prime_oneHundredSixtyTwoFD_14898929285702599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579298 : Nat.totient 191527235224657233256840579298 = 95763617405281613870623062000 := by
  rw [← show ((([(2, 1), (462521149, 1), (207047002757334706501, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_462521149, prime_oneHundredSixtyTwoFD_207047002757334706501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579299 : Nat.totient 191527235224657233256840579299 = 120919077111016549790387613360 := by
  rw [← show ((([(3, 2), (19, 1), (2659, 1), (421226894041107731343491, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_3, prime_oneHundredSixtyTwoFD_19, prime_oneHundredSixtyTwoFD_2659, prime_oneHundredSixtyTwoFD_421226894041107731343491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579300 : Nat.totient 191527235224657233256840579300 = 74251666269735085893929910400 := by
  rw [← show ((([(2, 2), (5, 2), (59, 1), (71, 1), (623106816923, 1), (733766155919, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_2, prime_oneHundredSixtyTwoFD_5, prime_oneHundredSixtyTwoFD_59, prime_oneHundredSixtyTwoFD_71, prime_oneHundredSixtyTwoFD_623106816923, prime_oneHundredSixtyTwoFD_733766155919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyTwoFD_191527235224657233256840579301 : Nat.totient 191527235224657233256840579301 = 189218696691077700552935855280 := by
  rw [← show ((([(83, 1), (192791, 1), (28928527039, 1), (413751298703, 1)] : List FactorBlock).map factorBlockValue).prod) = 191527235224657233256840579301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyTwoFD_83, prime_oneHundredSixtyTwoFD_192791, prime_oneHundredSixtyTwoFD_28928527039, prime_oneHundredSixtyTwoFD_413751298703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredSixtyTwoFD : certifiedKill 1 191527235224657233256840579199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579200, phi_oneHundredSixtyTwoFD_191527235224657233256840579201, phi_oneHundredSixtyTwoFD_191527235224657233256840579202,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579203, phi_oneHundredSixtyTwoFD_191527235224657233256840579204, phi_oneHundredSixtyTwoFD_191527235224657233256840579205,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579206, phi_oneHundredSixtyTwoFD_191527235224657233256840579207, phi_oneHundredSixtyTwoFD_191527235224657233256840579208,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579209, phi_oneHundredSixtyTwoFD_191527235224657233256840579210, phi_oneHundredSixtyTwoFD_191527235224657233256840579211,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579212, phi_oneHundredSixtyTwoFD_191527235224657233256840579213, phi_oneHundredSixtyTwoFD_191527235224657233256840579214,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579215, phi_oneHundredSixtyTwoFD_191527235224657233256840579216, phi_oneHundredSixtyTwoFD_191527235224657233256840579217,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579218, phi_oneHundredSixtyTwoFD_191527235224657233256840579219, phi_oneHundredSixtyTwoFD_191527235224657233256840579220,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579221, phi_oneHundredSixtyTwoFD_191527235224657233256840579222, phi_oneHundredSixtyTwoFD_191527235224657233256840579223,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579224, phi_oneHundredSixtyTwoFD_191527235224657233256840579225, phi_oneHundredSixtyTwoFD_191527235224657233256840579226,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579227, phi_oneHundredSixtyTwoFD_191527235224657233256840579228, phi_oneHundredSixtyTwoFD_191527235224657233256840579229,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579230, phi_oneHundredSixtyTwoFD_191527235224657233256840579231, phi_oneHundredSixtyTwoFD_191527235224657233256840579232,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579233, phi_oneHundredSixtyTwoFD_191527235224657233256840579234, phi_oneHundredSixtyTwoFD_191527235224657233256840579235,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579236, phi_oneHundredSixtyTwoFD_191527235224657233256840579237, phi_oneHundredSixtyTwoFD_191527235224657233256840579238,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579239, phi_oneHundredSixtyTwoFD_191527235224657233256840579240, phi_oneHundredSixtyTwoFD_191527235224657233256840579241,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579242, phi_oneHundredSixtyTwoFD_191527235224657233256840579243, phi_oneHundredSixtyTwoFD_191527235224657233256840579244,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579245, phi_oneHundredSixtyTwoFD_191527235224657233256840579246, phi_oneHundredSixtyTwoFD_191527235224657233256840579247,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579248, phi_oneHundredSixtyTwoFD_191527235224657233256840579249, phi_oneHundredSixtyTwoFD_191527235224657233256840579250,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579251, phi_oneHundredSixtyTwoFD_191527235224657233256840579252, phi_oneHundredSixtyTwoFD_191527235224657233256840579253,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579254, phi_oneHundredSixtyTwoFD_191527235224657233256840579255, phi_oneHundredSixtyTwoFD_191527235224657233256840579256,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579257, phi_oneHundredSixtyTwoFD_191527235224657233256840579258, phi_oneHundredSixtyTwoFD_191527235224657233256840579259,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579260, phi_oneHundredSixtyTwoFD_191527235224657233256840579261, phi_oneHundredSixtyTwoFD_191527235224657233256840579262,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579263, phi_oneHundredSixtyTwoFD_191527235224657233256840579264, phi_oneHundredSixtyTwoFD_191527235224657233256840579265,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579266, phi_oneHundredSixtyTwoFD_191527235224657233256840579267, phi_oneHundredSixtyTwoFD_191527235224657233256840579268,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579269, phi_oneHundredSixtyTwoFD_191527235224657233256840579270, phi_oneHundredSixtyTwoFD_191527235224657233256840579271,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579272, phi_oneHundredSixtyTwoFD_191527235224657233256840579273, phi_oneHundredSixtyTwoFD_191527235224657233256840579274,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579275, phi_oneHundredSixtyTwoFD_191527235224657233256840579276, phi_oneHundredSixtyTwoFD_191527235224657233256840579277,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579278, phi_oneHundredSixtyTwoFD_191527235224657233256840579279, phi_oneHundredSixtyTwoFD_191527235224657233256840579280,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579281, phi_oneHundredSixtyTwoFD_191527235224657233256840579282, phi_oneHundredSixtyTwoFD_191527235224657233256840579283,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579284, phi_oneHundredSixtyTwoFD_191527235224657233256840579285, phi_oneHundredSixtyTwoFD_191527235224657233256840579286,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579287, phi_oneHundredSixtyTwoFD_191527235224657233256840579288, phi_oneHundredSixtyTwoFD_191527235224657233256840579289,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579290, phi_oneHundredSixtyTwoFD_191527235224657233256840579291, phi_oneHundredSixtyTwoFD_191527235224657233256840579292,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579293, phi_oneHundredSixtyTwoFD_191527235224657233256840579294, phi_oneHundredSixtyTwoFD_191527235224657233256840579295,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579296, phi_oneHundredSixtyTwoFD_191527235224657233256840579297, phi_oneHundredSixtyTwoFD_191527235224657233256840579298,
    phi_oneHundredSixtyTwoFD_191527235224657233256840579299, phi_oneHundredSixtyTwoFD_191527235224657233256840579300, phi_oneHundredSixtyTwoFD_191527235224657233256840579301]

end TotientTailPeriodKiller
end Erdos249257
