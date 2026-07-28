import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredThirtyDXFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredThirtyDXFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredThirtyDXFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredThirtyDXFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredThirtyDXFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredThirtyDXFastPow a n * oneHundredThirtyDXFastPow a n * a else oneHundredThirtyDXFastPow a n * oneHundredThirtyDXFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredThirtyDX_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredThirtyDX_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredThirtyDX_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredThirtyDX_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredThirtyDX_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredThirtyDX_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredThirtyDX_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredThirtyDX_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredThirtyDX_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredThirtyDX_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredThirtyDX_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredThirtyDX_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredThirtyDX_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredThirtyDX_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredThirtyDX_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredThirtyDX_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredThirtyDX_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredThirtyDX_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredThirtyDX_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredThirtyDX_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredThirtyDX_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredThirtyDX_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredThirtyDX_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredThirtyDX_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredThirtyDX_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredThirtyDX_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredThirtyDX_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredThirtyDX_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredThirtyDX_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredThirtyDX_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredThirtyDX_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredThirtyDX_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredThirtyDX_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredThirtyDX_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredThirtyDX_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredThirtyDX_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredThirtyDX_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredThirtyDX_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredThirtyDX_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredThirtyDX_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredThirtyDX_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredThirtyDX_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredThirtyDX_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredThirtyDX_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredThirtyDX_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredThirtyDX_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredThirtyDX_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredThirtyDX_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredThirtyDX_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredThirtyDX_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredThirtyDX_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredThirtyDX_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredThirtyDX_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredThirtyDX_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredThirtyDX_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredThirtyDX_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredThirtyDX_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredThirtyDX_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredThirtyDX_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredThirtyDX_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredThirtyDX_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredThirtyDX_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredThirtyDX_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredThirtyDX_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredThirtyDX_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredThirtyDX_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredThirtyDX_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredThirtyDX_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredThirtyDX_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredThirtyDX_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredThirtyDX_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredThirtyDX_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredThirtyDX_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredThirtyDX_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredThirtyDX_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredThirtyDX_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredThirtyDX_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredThirtyDX_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredThirtyDX_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredThirtyDX_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredThirtyDX_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredThirtyDX_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredThirtyDX_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredThirtyDX_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredThirtyDX_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredThirtyDX_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredThirtyDX_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredThirtyDX_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredThirtyDX_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredThirtyDX_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredThirtyDX_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredThirtyDX_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredThirtyDX_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredThirtyDX_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredThirtyDX_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredThirtyDX_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredThirtyDX_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredThirtyDX_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredThirtyDX_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredThirtyDX_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredThirtyDX_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredThirtyDX_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredThirtyDX_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredThirtyDX_941 : Nat.Prime 941 := by norm_num

private theorem prime_oneHundredThirtyDX_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredThirtyDX_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredThirtyDX_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_oneHundredThirtyDX_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredThirtyDX_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_oneHundredThirtyDX_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredThirtyDX_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_oneHundredThirtyDX_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredThirtyDX_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_oneHundredThirtyDX_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredThirtyDX_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_oneHundredThirtyDX_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_oneHundredThirtyDX_1381 : Nat.Prime 1381 := by norm_num

private theorem prime_oneHundredThirtyDX_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_oneHundredThirtyDX_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_oneHundredThirtyDX_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_oneHundredThirtyDX_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_oneHundredThirtyDX_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_oneHundredThirtyDX_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_oneHundredThirtyDX_1699 : Nat.Prime 1699 := by norm_num

private theorem prime_oneHundredThirtyDX_1723 : Nat.Prime 1723 := by norm_num

private theorem prime_oneHundredThirtyDX_1759 : Nat.Prime 1759 := by norm_num

private theorem prime_oneHundredThirtyDX_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_oneHundredThirtyDX_1789 : Nat.Prime 1789 := by norm_num

private theorem prime_oneHundredThirtyDX_1801 : Nat.Prime 1801 := by norm_num

private theorem prime_oneHundredThirtyDX_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredThirtyDX_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_oneHundredThirtyDX_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_oneHundredThirtyDX_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_oneHundredThirtyDX_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_oneHundredThirtyDX_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_oneHundredThirtyDX_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredThirtyDX_2137 : Nat.Prime 2137 := by norm_num

private theorem prime_oneHundredThirtyDX_2267 : Nat.Prime 2267 := by norm_num

private theorem prime_oneHundredThirtyDX_2293 : Nat.Prime 2293 := by norm_num

private theorem prime_oneHundredThirtyDX_2339 : Nat.Prime 2339 := by norm_num

private theorem prime_oneHundredThirtyDX_2381 : Nat.Prime 2381 := by norm_num

private theorem prime_oneHundredThirtyDX_2389 : Nat.Prime 2389 := by norm_num

private theorem prime_oneHundredThirtyDX_2393 : Nat.Prime 2393 := by norm_num

private theorem prime_oneHundredThirtyDX_2459 : Nat.Prime 2459 := by norm_num

private theorem prime_oneHundredThirtyDX_2473 : Nat.Prime 2473 := by norm_num

private theorem prime_oneHundredThirtyDX_2477 : Nat.Prime 2477 := by norm_num

private theorem prime_oneHundredThirtyDX_2543 : Nat.Prime 2543 := by norm_num

private theorem prime_oneHundredThirtyDX_2551 : Nat.Prime 2551 := by norm_num

private theorem prime_oneHundredThirtyDX_2579 : Nat.Prime 2579 := by norm_num

private theorem prime_oneHundredThirtyDX_2593 : Nat.Prime 2593 := by norm_num

private theorem prime_oneHundredThirtyDX_2699 : Nat.Prime 2699 := by norm_num

private theorem prime_oneHundredThirtyDX_2777 : Nat.Prime 2777 := by norm_num

private theorem prime_oneHundredThirtyDX_2843 : Nat.Prime 2843 := by norm_num

private theorem prime_oneHundredThirtyDX_2861 : Nat.Prime 2861 := by norm_num

private theorem prime_oneHundredThirtyDX_2887 : Nat.Prime 2887 := by norm_num

private theorem prime_oneHundredThirtyDX_2897 : Nat.Prime 2897 := by norm_num

private theorem prime_oneHundredThirtyDX_2909 : Nat.Prime 2909 := by norm_num

private theorem prime_oneHundredThirtyDX_2939 : Nat.Prime 2939 := by norm_num

private theorem prime_oneHundredThirtyDX_2999 : Nat.Prime 2999 := by norm_num

private theorem prime_oneHundredThirtyDX_3011 : Nat.Prime 3011 := by norm_num

private theorem prime_oneHundredThirtyDX_3181 : Nat.Prime 3181 := by norm_num

private theorem prime_oneHundredThirtyDX_3271 : Nat.Prime 3271 := by norm_num

private theorem prime_oneHundredThirtyDX_3331 : Nat.Prime 3331 := by norm_num

private theorem prime_oneHundredThirtyDX_3347 : Nat.Prime 3347 := by norm_num

private theorem prime_oneHundredThirtyDX_3391 : Nat.Prime 3391 := by norm_num

private theorem prime_oneHundredThirtyDX_3517 : Nat.Prime 3517 := by norm_num

private theorem prime_oneHundredThirtyDX_3607 : Nat.Prime 3607 := by norm_num

private theorem prime_oneHundredThirtyDX_3727 : Nat.Prime 3727 := by norm_num

private theorem prime_oneHundredThirtyDX_3803 : Nat.Prime 3803 := by norm_num

private theorem prime_oneHundredThirtyDX_4001 : Nat.Prime 4001 := by norm_num

private theorem prime_oneHundredThirtyDX_4019 : Nat.Prime 4019 := by norm_num

private theorem prime_oneHundredThirtyDX_4201 : Nat.Prime 4201 := by norm_num

private theorem prime_oneHundredThirtyDX_4327 : Nat.Prime 4327 := by norm_num

private theorem prime_oneHundredThirtyDX_4357 : Nat.Prime 4357 := by norm_num

private theorem prime_oneHundredThirtyDX_4463 : Nat.Prime 4463 := by norm_num

private theorem prime_oneHundredThirtyDX_4651 : Nat.Prime 4651 := by norm_num

private theorem prime_oneHundredThirtyDX_4657 : Nat.Prime 4657 := by norm_num

private theorem prime_oneHundredThirtyDX_4691 : Nat.Prime 4691 := by norm_num

private theorem prime_oneHundredThirtyDX_4721 : Nat.Prime 4721 := by norm_num

private theorem prime_oneHundredThirtyDX_4733 : Nat.Prime 4733 := by norm_num

private theorem prime_oneHundredThirtyDX_4993 : Nat.Prime 4993 := by norm_num

private theorem prime_oneHundredThirtyDX_5237 : Nat.Prime 5237 := by norm_num

private theorem prime_oneHundredThirtyDX_5351 : Nat.Prime 5351 := by norm_num

private theorem prime_oneHundredThirtyDX_5711 : Nat.Prime 5711 := by norm_num

private theorem prime_oneHundredThirtyDX_6569 : Nat.Prime 6569 := by norm_num

private theorem prime_oneHundredThirtyDX_6829 : Nat.Prime 6829 := by norm_num

private theorem prime_oneHundredThirtyDX_6863 : Nat.Prime 6863 := by norm_num

private theorem prime_oneHundredThirtyDX_7027 : Nat.Prime 7027 := by norm_num

private theorem prime_oneHundredThirtyDX_7247 : Nat.Prime 7247 := by norm_num

private theorem prime_oneHundredThirtyDX_7669 : Nat.Prime 7669 := by norm_num

private theorem prime_oneHundredThirtyDX_7919 : Nat.Prime 7919 := by norm_num

private theorem prime_oneHundredThirtyDX_8147 : Nat.Prime 8147 := by norm_num

private theorem prime_oneHundredThirtyDX_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredThirtyDX_8317 : Nat.Prime 8317 := by norm_num

private theorem prime_oneHundredThirtyDX_8369 : Nat.Prime 8369 := by norm_num

private theorem prime_oneHundredThirtyDX_8521 : Nat.Prime 8521 := by norm_num

private theorem prime_oneHundredThirtyDX_8747 : Nat.Prime 8747 := by norm_num

private theorem prime_oneHundredThirtyDX_8839 : Nat.Prime 8839 := by norm_num

private theorem prime_oneHundredThirtyDX_9203 : Nat.Prime 9203 := by norm_num

private theorem prime_oneHundredThirtyDX_9439 : Nat.Prime 9439 := by norm_num

private theorem prime_oneHundredThirtyDX_9551 : Nat.Prime 9551 := by norm_num

private theorem prime_oneHundredThirtyDX_9631 : Nat.Prime 9631 := by norm_num

private theorem prime_oneHundredThirtyDX_9649 : Nat.Prime 9649 := by norm_num

private theorem prime_oneHundredThirtyDX_9719 : Nat.Prime 9719 := by norm_num

private theorem prime_oneHundredThirtyDX_9721 : Nat.Prime 9721 := by norm_num

private theorem prime_oneHundredThirtyDX_9857 : Nat.Prime 9857 := by norm_num

private theorem prime_oneHundredThirtyDX_10321 : Nat.Prime 10321 := by norm_num

private theorem prime_oneHundredThirtyDX_10859 : Nat.Prime 10859 := by norm_num

private theorem prime_oneHundredThirtyDX_11593 : Nat.Prime 11593 := by norm_num

private theorem prime_oneHundredThirtyDX_11681 : Nat.Prime 11681 := by norm_num

private theorem prime_oneHundredThirtyDX_12073 : Nat.Prime 12073 := by norm_num

private theorem prime_oneHundredThirtyDX_12451 : Nat.Prime 12451 := by norm_num

private theorem prime_oneHundredThirtyDX_12539 : Nat.Prime 12539 := by norm_num

private theorem prime_oneHundredThirtyDX_13037 : Nat.Prime 13037 := by norm_num

private theorem prime_oneHundredThirtyDX_14051 : Nat.Prime 14051 := by norm_num

private theorem prime_oneHundredThirtyDX_14107 : Nat.Prime 14107 := by norm_num

private theorem prime_oneHundredThirtyDX_14437 : Nat.Prime 14437 := by norm_num

private theorem prime_oneHundredThirtyDX_14591 : Nat.Prime 14591 := by norm_num

private theorem prime_oneHundredThirtyDX_14639 : Nat.Prime 14639 := by norm_num

private theorem prime_oneHundredThirtyDX_14713 : Nat.Prime 14713 := by norm_num

private theorem prime_oneHundredThirtyDX_14951 : Nat.Prime 14951 := by norm_num

private theorem prime_oneHundredThirtyDX_15017 : Nat.Prime 15017 := by norm_num

private theorem prime_oneHundredThirtyDX_15173 : Nat.Prime 15173 := by norm_num

private theorem prime_oneHundredThirtyDX_15269 : Nat.Prime 15269 := by norm_num

private theorem prime_oneHundredThirtyDX_16223 : Nat.Prime 16223 := by norm_num

private theorem prime_oneHundredThirtyDX_16981 : Nat.Prime 16981 := by norm_num

private theorem prime_oneHundredThirtyDX_17021 : Nat.Prime 17021 := by norm_num

private theorem prime_oneHundredThirtyDX_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredThirtyDX_17341 : Nat.Prime 17341 := by norm_num

private theorem prime_oneHundredThirtyDX_20297 : Nat.Prime 20297 := by norm_num

private theorem prime_oneHundredThirtyDX_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredThirtyDX_21061 : Nat.Prime 21061 := by norm_num

private theorem prime_oneHundredThirtyDX_21407 : Nat.Prime 21407 := by norm_num

private theorem prime_oneHundredThirtyDX_21881 : Nat.Prime 21881 := by norm_num

private theorem prime_oneHundredThirtyDX_22051 : Nat.Prime 22051 := by norm_num

private theorem prime_oneHundredThirtyDX_22283 : Nat.Prime 22283 := by norm_num

private theorem prime_oneHundredThirtyDX_23633 : Nat.Prime 23633 := by norm_num

private theorem prime_oneHundredThirtyDX_23971 : Nat.Prime 23971 := by norm_num

private theorem prime_oneHundredThirtyDX_24181 : Nat.Prime 24181 := by norm_num

private theorem prime_oneHundredThirtyDX_24623 : Nat.Prime 24623 := by norm_num

private theorem prime_oneHundredThirtyDX_26921 : Nat.Prime 26921 := by norm_num

private theorem prime_oneHundredThirtyDX_28649 : Nat.Prime 28649 := by norm_num

private theorem prime_oneHundredThirtyDX_28729 : Nat.Prime 28729 := by norm_num

private theorem prime_oneHundredThirtyDX_30539 : Nat.Prime 30539 := by norm_num

private theorem prime_oneHundredThirtyDX_30703 : Nat.Prime 30703 := by norm_num

private theorem prime_oneHundredThirtyDX_31547 : Nat.Prime 31547 := by norm_num

private theorem prime_oneHundredThirtyDX_32479 : Nat.Prime 32479 := by norm_num

private theorem prime_oneHundredThirtyDX_32561 : Nat.Prime 32561 := by norm_num

private theorem prime_oneHundredThirtyDX_32717 : Nat.Prime 32717 := by norm_num

private theorem prime_oneHundredThirtyDX_32779 : Nat.Prime 32779 := by norm_num

private theorem prime_oneHundredThirtyDX_33739 : Nat.Prime 33739 := by norm_num

private theorem prime_oneHundredThirtyDX_33797 : Nat.Prime 33797 := by norm_num

private theorem prime_oneHundredThirtyDX_36097 : Nat.Prime 36097 := by norm_num

private theorem prime_oneHundredThirtyDX_36269 : Nat.Prime 36269 := by norm_num

private theorem prime_oneHundredThirtyDX_37181 : Nat.Prime 37181 := by norm_num

private theorem prime_oneHundredThirtyDX_37573 : Nat.Prime 37573 := by norm_num

private theorem prime_oneHundredThirtyDX_37717 : Nat.Prime 37717 := by norm_num

private theorem prime_oneHundredThirtyDX_39679 : Nat.Prime 39679 := by norm_num

private theorem prime_oneHundredThirtyDX_41081 : Nat.Prime 41081 := by norm_num

private theorem prime_oneHundredThirtyDX_41627 : Nat.Prime 41627 := by norm_num

private theorem prime_oneHundredThirtyDX_42793 : Nat.Prime 42793 := by norm_num

private theorem prime_oneHundredThirtyDX_43891 : Nat.Prime 43891 := by norm_num

private theorem prime_oneHundredThirtyDX_44501 : Nat.Prime 44501 := by norm_num

private theorem prime_oneHundredThirtyDX_44543 : Nat.Prime 44543 := by norm_num

private theorem prime_oneHundredThirtyDX_45497 : Nat.Prime 45497 := by norm_num

private theorem prime_oneHundredThirtyDX_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredThirtyDX_48823 : Nat.Prime 48823 := by norm_num

private theorem prime_oneHundredThirtyDX_49807 : Nat.Prime 49807 := by norm_num

private theorem prime_oneHundredThirtyDX_49823 : Nat.Prime 49823 := by norm_num

private theorem prime_oneHundredThirtyDX_51413 : Nat.Prime 51413 := by norm_num

private theorem prime_oneHundredThirtyDX_53897 : Nat.Prime 53897 := by norm_num

private theorem prime_oneHundredThirtyDX_54419 : Nat.Prime 54419 := by norm_num

private theorem prime_oneHundredThirtyDX_54583 : Nat.Prime 54583 := by norm_num

private theorem prime_oneHundredThirtyDX_55351 : Nat.Prime 55351 := by norm_num

private theorem prime_oneHundredThirtyDX_56783 : Nat.Prime 56783 := by norm_num

private theorem prime_oneHundredThirtyDX_63901 : Nat.Prime 63901 := by norm_num

private theorem prime_oneHundredThirtyDX_65837 : Nat.Prime 65837 := by norm_num

private theorem prime_oneHundredThirtyDX_68947 : Nat.Prime 68947 := by norm_num

private theorem prime_oneHundredThirtyDX_69151 : Nat.Prime 69151 := by norm_num

private theorem prime_oneHundredThirtyDX_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredThirtyDX_71171 : Nat.Prime 71171 := by norm_num

private theorem prime_oneHundredThirtyDX_79379 : Nat.Prime 79379 := by norm_num

private theorem prime_oneHundredThirtyDX_80071 : Nat.Prime 80071 := by norm_num

private theorem prime_oneHundredThirtyDX_84509 : Nat.Prime 84509 := by norm_num

private theorem prime_oneHundredThirtyDX_86117 : Nat.Prime 86117 := by norm_num

private theorem prime_oneHundredThirtyDX_86389 : Nat.Prime 86389 := by norm_num

private theorem prime_oneHundredThirtyDX_86923 : Nat.Prime 86923 := by norm_num

private theorem prime_oneHundredThirtyDX_88423 : Nat.Prime 88423 := by norm_num

private theorem prime_oneHundredThirtyDX_89231 : Nat.Prime 89231 := by norm_num

private theorem prime_oneHundredThirtyDX_91397 : Nat.Prime 91397 := by norm_num

private theorem prime_oneHundredThirtyDX_95257 : Nat.Prime 95257 := by norm_num

private theorem prime_oneHundredThirtyDX_95923 : Nat.Prime 95923 := by norm_num

private theorem prime_oneHundredThirtyDX_96517 : Nat.Prime 96517 := by norm_num

private theorem prime_oneHundredThirtyDX_96697 : Nat.Prime 96697 := by norm_num

private theorem prime_oneHundredThirtyDX_103813 : Nat.Prime 103813 := by norm_num

private theorem prime_oneHundredThirtyDX_105767 : Nat.Prime 105767 := by norm_num

private theorem prime_oneHundredThirtyDX_111043 : Nat.Prime 111043 := by norm_num

private theorem prime_oneHundredThirtyDX_113147 : Nat.Prime 113147 := by norm_num

private theorem prime_oneHundredThirtyDX_113171 : Nat.Prime 113171 := by norm_num

private theorem prime_oneHundredThirtyDX_118739 : Nat.Prime 118739 := by norm_num

private theorem prime_oneHundredThirtyDX_119929 : Nat.Prime 119929 := by norm_num

private theorem prime_oneHundredThirtyDX_120661 : Nat.Prime 120661 := by norm_num

private theorem prime_oneHundredThirtyDX_125539 : Nat.Prime 125539 := by norm_num

private theorem prime_oneHundredThirtyDX_160183 : Nat.Prime 160183 := by norm_num

private theorem prime_oneHundredThirtyDX_169003 : Nat.Prime 169003 := by norm_num

private theorem prime_oneHundredThirtyDX_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredThirtyDX_172313 : Nat.Prime 172313 := by norm_num

private theorem prime_oneHundredThirtyDX_185153 : Nat.Prime 185153 := by norm_num

private theorem prime_oneHundredThirtyDX_204859 : Nat.Prime 204859 := by norm_num

private theorem prime_oneHundredThirtyDX_212203 : Nat.Prime 212203 := by norm_num

private theorem prime_oneHundredThirtyDX_214483 : Nat.Prime 214483 := by norm_num

private theorem prime_oneHundredThirtyDX_215191 : Nat.Prime 215191 := by norm_num

private theorem prime_oneHundredThirtyDX_215863 : Nat.Prime 215863 := by norm_num

private theorem prime_oneHundredThirtyDX_216371 : Nat.Prime 216371 := by norm_num

private theorem prime_oneHundredThirtyDX_237467 : Nat.Prime 237467 := by norm_num

private theorem prime_oneHundredThirtyDX_238531 : Nat.Prime 238531 := by norm_num

private theorem prime_oneHundredThirtyDX_244451 : Nat.Prime 244451 := by norm_num

private theorem prime_oneHundredThirtyDX_251897 : Nat.Prime 251897 := by norm_num

private theorem prime_oneHundredThirtyDX_256211 : Nat.Prime 256211 := by norm_num

private theorem prime_oneHundredThirtyDX_269089 : Nat.Prime 269089 := by norm_num

private theorem prime_oneHundredThirtyDX_279029 : Nat.Prime 279029 := by norm_num

private theorem prime_oneHundredThirtyDX_303997 : Nat.Prime 303997 := by norm_num

private theorem prime_oneHundredThirtyDX_305101 : Nat.Prime 305101 := by norm_num

private theorem prime_oneHundredThirtyDX_306349 : Nat.Prime 306349 := by norm_num

private theorem prime_oneHundredThirtyDX_321187 : Nat.Prime 321187 := by norm_num

private theorem prime_oneHundredThirtyDX_327289 : Nat.Prime 327289 := by norm_num

private theorem prime_oneHundredThirtyDX_338543 : Nat.Prime 338543 := by norm_num

private theorem prime_oneHundredThirtyDX_346417 : Nat.Prime 346417 := by norm_num

private theorem prime_oneHundredThirtyDX_379033 : Nat.Prime 379033 := by norm_num

private theorem prime_oneHundredThirtyDX_395611 : Nat.Prime 395611 := by norm_num

private theorem prime_oneHundredThirtyDX_429223 : Nat.Prime 429223 := by norm_num

private theorem prime_oneHundredThirtyDX_433151 : Nat.Prime 433151 := by norm_num

private theorem prime_oneHundredThirtyDX_445597 : Nat.Prime 445597 := by norm_num

private theorem prime_oneHundredThirtyDX_509939 : Nat.Prime 509939 := by norm_num

private theorem prime_oneHundredThirtyDX_517721 : Nat.Prime 517721 := by norm_num

private theorem prime_oneHundredThirtyDX_537157 : Nat.Prime 537157 := by norm_num

private theorem prime_oneHundredThirtyDX_583417 : Nat.Prime 583417 := by norm_num

private theorem prime_oneHundredThirtyDX_595261 : Nat.Prime 595261 := by norm_num

private theorem prime_oneHundredThirtyDX_607213 : Nat.Prime 607213 := by norm_num

private theorem prime_oneHundredThirtyDX_633883 : Nat.Prime 633883 := by norm_num

private theorem prime_oneHundredThirtyDX_678593 : Nat.Prime 678593 := by norm_num

private theorem prime_oneHundredThirtyDX_702239 : Nat.Prime 702239 := by norm_num

private theorem prime_oneHundredThirtyDX_738373 : Nat.Prime 738373 := by norm_num

private theorem prime_oneHundredThirtyDX_750653 : Nat.Prime 750653 := by norm_num

private theorem prime_oneHundredThirtyDX_767537 : Nat.Prime 767537 := by norm_num

private theorem prime_oneHundredThirtyDX_868423 : Nat.Prime 868423 := by norm_num

private theorem prime_oneHundredThirtyDX_921517 : Nat.Prime 921517 := by norm_num

private theorem prime_oneHundredThirtyDX_965749 : Nat.Prime 965749 := by norm_num

private theorem prime_oneHundredThirtyDX_967481 : Nat.Prime 967481 := by norm_num

private theorem prime_oneHundredThirtyDX_1022677 : Nat.Prime 1022677 := by norm_num

private theorem prime_oneHundredThirtyDX_1026101 : Nat.Prime 1026101 := by norm_num

private theorem prime_oneHundredThirtyDX_1035707 : Nat.Prime 1035707 := by norm_num

private theorem prime_oneHundredThirtyDX_1275749 : Nat.Prime 1275749 := by norm_num

private theorem prime_oneHundredThirtyDX_1283701 : Nat.Prime 1283701 := by norm_num

private theorem prime_oneHundredThirtyDX_1315283 : Nat.Prime 1315283 := by norm_num

private theorem prime_oneHundredThirtyDX_1342519 : Nat.Prime 1342519 := by norm_num

private theorem prime_oneHundredThirtyDX_1345303 : Nat.Prime 1345303 := by norm_num

private theorem prime_oneHundredThirtyDX_1399271 : Nat.Prime 1399271 := by norm_num

private theorem prime_oneHundredThirtyDX_1439927 : Nat.Prime 1439927 := by norm_num

private theorem prime_oneHundredThirtyDX_1442863 : Nat.Prime 1442863 := by norm_num

private theorem prime_oneHundredThirtyDX_1798523 : Nat.Prime 1798523 := by norm_num

private theorem prime_oneHundredThirtyDX_1909981 : Nat.Prime 1909981 := by norm_num

private theorem prime_oneHundredThirtyDX_1964981 : Nat.Prime 1964981 := by norm_num

private theorem prime_oneHundredThirtyDX_1997243 : Nat.Prime 1997243 := by norm_num

private theorem prime_oneHundredThirtyDX_2099093 : Nat.Prime 2099093 := by norm_num

private theorem prime_oneHundredThirtyDX_2103029 : Nat.Prime 2103029 := by norm_num

private theorem prime_oneHundredThirtyDX_2106673 : Nat.Prime 2106673 := by norm_num

private theorem prime_oneHundredThirtyDX_2199401 : Nat.Prime 2199401 := by norm_num

private theorem prime_oneHundredThirtyDX_2242777 : Nat.Prime 2242777 := by norm_num

private theorem prime_oneHundredThirtyDX_2254793 : Nat.Prime 2254793 := by norm_num

private theorem prime_oneHundredThirtyDX_2557111 : Nat.Prime 2557111 := by norm_num

private theorem prime_oneHundredThirtyDX_2632627 : Nat.Prime 2632627 := by norm_num

private theorem prime_oneHundredThirtyDX_2677099 : Nat.Prime 2677099 := by norm_num

private theorem prime_oneHundredThirtyDX_2679647 : Nat.Prime 2679647 := by norm_num

private theorem prime_oneHundredThirtyDX_2820541 : Nat.Prime 2820541 := by norm_num

private theorem prime_oneHundredThirtyDX_2821573 : Nat.Prime 2821573 := by norm_num

private theorem prime_oneHundredThirtyDX_2996629 : Nat.Prime 2996629 := by norm_num

private theorem prime_oneHundredThirtyDX_3059143 : Nat.Prime 3059143 := by norm_num

private theorem prime_oneHundredThirtyDX_3102383 : Nat.Prime 3102383 := by norm_num

private theorem prime_oneHundredThirtyDX_3114971 : Nat.Prime 3114971 := by norm_num

private theorem prime_oneHundredThirtyDX_3431221 : Nat.Prime 3431221 := by norm_num

private theorem prime_oneHundredThirtyDX_3599009 : Nat.Prime 3599009 := by norm_num

private theorem prime_oneHundredThirtyDX_3611317 : Nat.Prime 3611317 := by norm_num

private theorem prime_oneHundredThirtyDX_3638827 : Nat.Prime 3638827 := by norm_num

private theorem prime_oneHundredThirtyDX_4015841 : Nat.Prime 4015841 := by norm_num

private theorem prime_oneHundredThirtyDX_4963349 : Nat.Prime 4963349 := by norm_num

private theorem prime_oneHundredThirtyDX_5202511 : Nat.Prime 5202511 := by norm_num

private theorem prime_oneHundredThirtyDX_5342503 : Nat.Prime 5342503 := by norm_num

private theorem prime_oneHundredThirtyDX_5401373 : Nat.Prime 5401373 := by norm_num

private theorem prime_oneHundredThirtyDX_6310039 : Nat.Prime 6310039 := by norm_num

private theorem prime_oneHundredThirtyDX_6346187 : Nat.Prime 6346187 := by norm_num

private theorem prime_oneHundredThirtyDX_6572983 : Nat.Prime 6572983 := by norm_num

private theorem prime_oneHundredThirtyDX_6647959 : Nat.Prime 6647959 := by norm_num

private theorem prime_oneHundredThirtyDX_6931649 : Nat.Prime 6931649 := by norm_num

private theorem prime_oneHundredThirtyDX_7631857 : Nat.Prime 7631857 := by norm_num

private theorem prime_oneHundredThirtyDX_8302403 : Nat.Prime 8302403 := by norm_num

private theorem prime_oneHundredThirtyDX_8494391 : Nat.Prime 8494391 := by norm_num

private theorem prime_oneHundredThirtyDX_8518681 : Nat.Prime 8518681 := by norm_num

private theorem prime_oneHundredThirtyDX_8802841 : Nat.Prime 8802841 := by norm_num

private theorem prime_oneHundredThirtyDX_9554807 : Nat.Prime 9554807 := by norm_num

private theorem prime_oneHundredThirtyDX_9890501 : Nat.Prime 9890501 := by norm_num

private theorem prime_oneHundredThirtyDX_10320283 : Nat.Prime 10320283 := by norm_num

private theorem prime_oneHundredThirtyDX_10399843 : Nat.Prime 10399843 := by norm_num

private theorem prime_oneHundredThirtyDX_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredThirtyDX_12718483 : Nat.Prime 12718483 := by norm_num

private theorem prime_oneHundredThirtyDX_13151923 : Nat.Prime 13151923 := by norm_num

private theorem prime_oneHundredThirtyDX_13617913 : Nat.Prime 13617913 := by norm_num

private theorem prime_oneHundredThirtyDX_14692609 : Nat.Prime 14692609 := by norm_num

private theorem prime_oneHundredThirtyDX_16235579 : Nat.Prime 16235579 := by norm_num

private theorem prime_oneHundredThirtyDX_16416293 : Nat.Prime 16416293 := by norm_num

private theorem prime_oneHundredThirtyDX_17709449 : Nat.Prime 17709449 := by norm_num

private theorem prime_oneHundredThirtyDX_18719203 : Nat.Prime 18719203 := by norm_num

private theorem prime_oneHundredThirtyDX_19773913 : Nat.Prime 19773913 := by norm_num

private theorem prime_oneHundredThirtyDX_19967261 : Nat.Prime 19967261 := by norm_num

private theorem prime_oneHundredThirtyDX_20182913 : Nat.Prime 20182913 := by norm_num

private theorem prime_oneHundredThirtyDX_21724111 : Nat.Prime 21724111 := by norm_num

private theorem prime_oneHundredThirtyDX_22337671 : Nat.Prime 22337671 := by norm_num

private theorem prime_oneHundredThirtyDX_23683529 : Nat.Prime 23683529 := by norm_num

private theorem prime_oneHundredThirtyDX_24312413 : Nat.Prime 24312413 := by norm_num

private theorem prime_oneHundredThirtyDX_25407757 : Nat.Prime 25407757 := by norm_num

private theorem prime_oneHundredThirtyDX_25470667 : Nat.Prime 25470667 := by norm_num

private theorem prime_oneHundredThirtyDX_25923907 : Nat.Prime 25923907 := by norm_num

private theorem prime_oneHundredThirtyDX_28405261 : Nat.Prime 28405261 := by norm_num

private theorem prime_oneHundredThirtyDX_33624103 : Nat.Prime 33624103 := by
  apply lucas_primality 33624103 (3 : ZMod 33624103)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (51413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (51413, 1)] : List FactorBlock).map factorBlockValue).prod) = 33624103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_109
      · exact prime_oneHundredThirtyDX_51413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 33624103) ^ 16812051 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 33624103) ^ 11208034 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 33624103) ^ 308478 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 33624103) ^ 654 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_35037377 : Nat.Prime 35037377 := by
  apply lucas_primality 35037377 (5 : ZMod 35037377)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (11, 1), (157, 1), (317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (11, 1), (157, 1), (317, 1)] : List FactorBlock).map factorBlockValue).prod) = 35037377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_157
      · exact prime_oneHundredThirtyDX_317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 35037377) ^ 17518688 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 35037377) ^ 3185216 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 35037377) ^ 223168 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 35037377) ^ 110528 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_37288723 : Nat.Prime 37288723 := by
  apply lucas_primality 37288723 (3 : ZMod 37288723)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (31, 2), (223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (31, 2), (223, 1)] : List FactorBlock).map factorBlockValue).prod) = 37288723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_29
      · exact prime_oneHundredThirtyDX_31
      · exact prime_oneHundredThirtyDX_223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37288723) ^ 18644361 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 37288723) ^ 12429574 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 37288723) ^ 1285818 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 37288723) ^ 1202862 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 37288723) ^ 167214 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_37574699 : Nat.Prime 37574699 := by
  apply lucas_primality 37574699 (2 : ZMod 37574699)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (109, 1), (24623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (109, 1), (24623, 1)] : List FactorBlock).map factorBlockValue).prod) = 37574699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_109
      · exact prime_oneHundredThirtyDX_24623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37574699) ^ 18787349 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 37574699) ^ 5367814 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 37574699) ^ 344722 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 37574699) ^ 1526 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_38353151 : Nat.Prime 38353151 := by
  apply lucas_primality 38353151 (7 : ZMod 38353151)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (137, 1), (509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (137, 1), (509, 1)] : List FactorBlock).map factorBlockValue).prod) = 38353151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_137
      · exact prime_oneHundredThirtyDX_509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 38353151) ^ 19176575 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 38353151) ^ 7670630 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 38353151) ^ 3486650 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 38353151) ^ 279950 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 38353151) ^ 75350 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_39994159 : Nat.Prime 39994159 := by
  apply lucas_primality 39994159 (6 : ZMod 39994159)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (223, 1), (421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (223, 1), (421, 1)] : List FactorBlock).map factorBlockValue).prod) = 39994159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_71
      · exact prime_oneHundredThirtyDX_223
      · exact prime_oneHundredThirtyDX_421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 39994159) ^ 19997079 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 39994159) ^ 13331386 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 39994159) ^ 563298 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 39994159) ^ 179346 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 39994159) ^ 94998 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_42474407 : Nat.Prime 42474407 := by
  apply lucas_primality 42474407 (5 : ZMod 42474407)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (571, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (571, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod) = 42474407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_571
      · exact prime_oneHundredThirtyDX_2861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42474407) ^ 21237203 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 42474407) ^ 3267262 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 42474407) ^ 74386 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 42474407) ^ 14846 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_45902981 : Nat.Prime 45902981 := by
  apply lucas_primality 45902981 (2 : ZMod 45902981)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (103, 1), (22283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (103, 1), (22283, 1)] : List FactorBlock).map factorBlockValue).prod) = 45902981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_103
      · exact prime_oneHundredThirtyDX_22283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45902981) ^ 22951490 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 45902981) ^ 9180596 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 45902981) ^ 445660 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 45902981) ^ 2060 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_46491397 : Nat.Prime 46491397 := by
  apply lucas_primality 46491397 (6 : ZMod 46491397)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (17, 1), (4651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (17, 1), (4651, 1)] : List FactorBlock).map factorBlockValue).prod) = 46491397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_4651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 46491397) ^ 23245698 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 46491397) ^ 15497132 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 46491397) ^ 6641628 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 46491397) ^ 2734788 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 46491397) ^ 9996 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_48503657 : Nat.Prime 48503657 := by
  apply lucas_primality 48503657 (3 : ZMod 48503657)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (41, 1), (43, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (41, 1), (43, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) = 48503657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_41
      · exact prime_oneHundredThirtyDX_43
      · exact prime_oneHundredThirtyDX_181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48503657) ^ 24251828 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 2552824 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 1183016 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 1127992 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 267976 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_50170357 : Nat.Prime 50170357 := by
  apply lucas_primality 50170357 (2 : ZMod 50170357)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (941, 1), (1481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (941, 1), (1481, 1)] : List FactorBlock).map factorBlockValue).prod) = 50170357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_941
      · exact prime_oneHundredThirtyDX_1481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 50170357) ^ 25085178 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50170357) ^ 16723452 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50170357) ^ 53316 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50170357) ^ 33876 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_51923327 : Nat.Prime 51923327 := by
  apply lucas_primality 51923327 (7 : ZMod 51923327)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (31, 1), (9203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (31, 1), (9203, 1)] : List FactorBlock).map factorBlockValue).prod) = 51923327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_31
      · exact prime_oneHundredThirtyDX_9203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 51923327) ^ 25961663 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 7417618 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 3994102 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 1674946 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 5642 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_52025111 : Nat.Prime 52025111 := by
  apply lucas_primality 52025111 (13 : ZMod 52025111)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5202511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5202511, 1)] : List FactorBlock).map factorBlockValue).prod) = 52025111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_5202511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 52025111) ^ 26012555 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 52025111) ^ 10405022 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 52025111) ^ 10 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_52864081 : Nat.Prime 52864081 := by
  apply lucas_primality 52864081 (17 : ZMod 52864081)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) = 52864081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_11593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 52864081) ^ 26432040 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 17621360 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 10572816 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 2782320 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 4560 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_59899309 : Nat.Prime 59899309 := by
  apply lucas_primality 59899309 (11 : ZMod 59899309)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (643, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (643, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 59899309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_643
      · exact prime_oneHundredThirtyDX_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 59899309) ^ 29949654 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 59899309) ^ 19966436 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 59899309) ^ 8557044 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 59899309) ^ 93156 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 59899309) ^ 54012 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_1811
      · exact prime_oneHundredThirtyDX_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_60852769 : Nat.Prime 60852769 := by
  apply lucas_primality 60852769 (7 : ZMod 60852769)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (633883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (633883, 1)] : List FactorBlock).map factorBlockValue).prod) = 60852769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_633883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 60852769) ^ 30426384 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 60852769) ^ 20284256 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 60852769) ^ 96 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_63200191 : Nat.Prime 63200191 := by
  apply lucas_primality 63200191 (3 : ZMod 63200191)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2106673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2106673, 1)] : List FactorBlock).map factorBlockValue).prod) = 63200191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_2106673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 63200191) ^ 31600095 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 63200191) ^ 21066730 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 63200191) ^ 12640038 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 63200191) ^ 30 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_75825557 : Nat.Prime 75825557 := by
  apply lucas_primality 75825557 (2 : ZMod 75825557)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (151, 1), (125539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (151, 1), (125539, 1)] : List FactorBlock).map factorBlockValue).prod) = 75825557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_151
      · exact prime_oneHundredThirtyDX_125539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75825557) ^ 37912778 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 75825557) ^ 502156 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 75825557) ^ 604 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_86482499 : Nat.Prime 86482499 := by
  apply lucas_primality 86482499 (2 : ZMod 86482499)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (821, 1), (1699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (821, 1), (1699, 1)] : List FactorBlock).map factorBlockValue).prod) = 86482499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_31
      · exact prime_oneHundredThirtyDX_821
      · exact prime_oneHundredThirtyDX_1699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 86482499) ^ 43241249 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 86482499) ^ 2789758 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 86482499) ^ 105338 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 86482499) ^ 50902 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_88846619 : Nat.Prime 88846619 := by
  apply lucas_primality 88846619 (2 : ZMod 88846619)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (6346187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (6346187, 1)] : List FactorBlock).map factorBlockValue).prod) = 88846619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_6346187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 88846619) ^ 44423309 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 88846619) ^ 12692374 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 88846619) ^ 14 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_93237031 : Nat.Prime 93237031 := by
  apply lucas_primality 93237031 (3 : ZMod 93237031)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (29, 1), (139, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (29, 1), (139, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) = 93237031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_29
      · exact prime_oneHundredThirtyDX_139
      · exact prime_oneHundredThirtyDX_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 93237031) ^ 46618515 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 93237031) ^ 31079010 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 93237031) ^ 18647406 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 93237031) ^ 3215070 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 93237031) ^ 670770 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 93237031) ^ 362790 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_95225759 : Nat.Prime 95225759 := by
  apply lucas_primality 95225759 (13 : ZMod 95225759)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (61, 1), (41081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (61, 1), (41081, 1)] : List FactorBlock).map factorBlockValue).prod) = 95225759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_61
      · exact prime_oneHundredThirtyDX_41081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 95225759) ^ 47612879 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 95225759) ^ 5011882 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 95225759) ^ 1561078 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 95225759) ^ 2318 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_103890979 : Nat.Prime 103890979 := by
  apply lucas_primality 103890979 (2 : ZMod 103890979)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (113171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (113171, 1)] : List FactorBlock).map factorBlockValue).prod) = 103890979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_113171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 103890979) ^ 51945489 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 103890979) ^ 34630326 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 103890979) ^ 6111234 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 103890979) ^ 918 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_104050223 : Nat.Prime 104050223 := by
  apply lucas_primality 104050223 (5 : ZMod 104050223)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (52025111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (52025111, 1)] : List FactorBlock).map factorBlockValue).prod) = 104050223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_52025111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 104050223) ^ 52025111 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 104050223) ^ 2 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_112315219 : Nat.Prime 112315219 := by
  apply lucas_primality 112315219 (2 : ZMod 112315219)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (18719203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (18719203, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_18719203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 112315219) ^ 56157609 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 112315219) ^ 37438406 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 112315219) ^ 6 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_119487457 : Nat.Prime 119487457 := by
  apply lucas_primality 119487457 (5 : ZMod 119487457)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (11, 1), (37717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (11, 1), (37717, 1)] : List FactorBlock).map factorBlockValue).prod) = 119487457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_37717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 119487457) ^ 59743728 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 119487457) ^ 39829152 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 119487457) ^ 10862496 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 119487457) ^ 3168 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_125159497 : Nat.Prime 125159497 := by
  apply lucas_primality 125159497 (13 : ZMod 125159497)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 2), (47, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 2), (47, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) = 125159497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_47
      · exact prime_oneHundredThirtyDX_131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 125159497) ^ 62579748 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 125159497) ^ 41719832 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 125159497) ^ 17879928 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 125159497) ^ 11378136 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 125159497) ^ 2662968 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 125159497) ^ 955416 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_126256447 : Nat.Prime 126256447 := by
  apply lucas_primality 126256447 (3 : ZMod 126256447)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (83, 1), (84509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (83, 1), (84509, 1)] : List FactorBlock).map factorBlockValue).prod) = 126256447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_83
      · exact prime_oneHundredThirtyDX_84509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 126256447) ^ 63128223 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 126256447) ^ 42085482 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 126256447) ^ 1521162 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 126256447) ^ 1494 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_142641539 : Nat.Prime 142641539 := by
  apply lucas_primality 142641539 (2 : ZMod 142641539)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (238531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (238531, 1)] : List FactorBlock).map factorBlockValue).prod) = 142641539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_23
      · exact prime_oneHundredThirtyDX_238531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 142641539) ^ 71320769 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 142641539) ^ 10972426 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 142641539) ^ 6201806 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 142641539) ^ 598 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_148186273 : Nat.Prime 148186273 := by
  apply lucas_primality 148186273 (5 : ZMod 148186273)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (118739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (118739, 1)] : List FactorBlock).map factorBlockValue).prod) = 148186273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_118739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 148186273) ^ 74093136 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 148186273) ^ 49395424 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 148186273) ^ 11398944 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 148186273) ^ 1248 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_168129629 : Nat.Prime 168129629 := by
  apply lucas_primality 168129629 (2 : ZMod 168129629)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 2), (30703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 2), (30703, 1)] : List FactorBlock).map factorBlockValue).prod) = 168129629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_37
      · exact prime_oneHundredThirtyDX_30703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 168129629) ^ 84064814 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 168129629) ^ 4544044 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 168129629) ^ 5476 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_185423809 : Nat.Prime 185423809 := by
  apply lucas_primality 185423809 (11 : ZMod 185423809)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (965749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (965749, 1)] : List FactorBlock).map factorBlockValue).prod) = 185423809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_965749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 185423809) ^ 92711904 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 185423809) ^ 61807936 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 185423809) ^ 192 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_196066613 : Nat.Prime 196066613 := by
  apply lucas_primality 196066613 (2 : ZMod 196066613)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (73, 1), (95923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (73, 1), (95923, 1)] : List FactorBlock).map factorBlockValue).prod) = 196066613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_73
      · exact prime_oneHundredThirtyDX_95923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 196066613) ^ 98033306 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 196066613) ^ 28009516 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 196066613) ^ 2685844 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 196066613) ^ 2044 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_199486121 : Nat.Prime 199486121 := by
  apply lucas_primality 199486121 (6 : ZMod 199486121)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (293, 1), (17021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (293, 1), (17021, 1)] : List FactorBlock).map factorBlockValue).prod) = 199486121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_293
      · exact prime_oneHundredThirtyDX_17021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 199486121) ^ 99743060 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 199486121) ^ 39897224 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 199486121) ^ 680840 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 199486121) ^ 11720 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_210430769 : Nat.Prime 210430769 := by
  apply lucas_primality 210430769 (3 : ZMod 210430769)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13151923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13151923, 1)] : List FactorBlock).map factorBlockValue).prod) = 210430769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_13151923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 210430769) ^ 105215384 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 210430769) ^ 16 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_215069383 : Nat.Prime 215069383 := by
  apply lucas_primality 215069383 (5 : ZMod 215069383)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (31, 1), (37, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (31, 1), (37, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) = 215069383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_31
      · exact prime_oneHundredThirtyDX_37
      · exact prime_oneHundredThirtyDX_947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 215069383) ^ 107534691 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 215069383) ^ 71689794 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 215069383) ^ 19551762 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 215069383) ^ 6937722 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 215069383) ^ 5812686 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 215069383) ^ 227106 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_244642639 : Nat.Prime 244642639 := by
  apply lucas_primality 244642639 (3 : ZMod 244642639)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (1315283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (1315283, 1)] : List FactorBlock).map factorBlockValue).prod) = 244642639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_31
      · exact prime_oneHundredThirtyDX_1315283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 244642639) ^ 122321319 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 244642639) ^ 81547546 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 244642639) ^ 7891698 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 244642639) ^ 186 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_270871009 : Nat.Prime 270871009 := by
  apply lucas_primality 270871009 (7 : ZMod 270871009)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (2821573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (2821573, 1)] : List FactorBlock).map factorBlockValue).prod) = 270871009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_2821573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 270871009) ^ 135435504 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 270871009) ^ 90290336 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 270871009) ^ 96 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_278764481 : Nat.Prime 278764481 := by
  apply lucas_primality 278764481 (3 : ZMod 278764481)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (569, 1), (1531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (569, 1), (1531, 1)] : List FactorBlock).map factorBlockValue).prod) = 278764481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_569
      · exact prime_oneHundredThirtyDX_1531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 278764481) ^ 139382240 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 278764481) ^ 55752896 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 278764481) ^ 489920 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 278764481) ^ 182080 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_346226141 : Nat.Prime 346226141 := by
  apply lucas_primality 346226141 (2 : ZMod 346226141)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (41, 1), (32479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (41, 1), (32479, 1)] : List FactorBlock).map factorBlockValue).prod) = 346226141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_41
      · exact prime_oneHundredThirtyDX_32479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 346226141) ^ 173113070 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 346226141) ^ 69245228 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 346226141) ^ 26632780 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 346226141) ^ 8444540 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 346226141) ^ 10660 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_349996873 : Nat.Prime 349996873 := by
  apply lucas_primality 349996873 (11 : ZMod 349996873)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (767537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (767537, 1)] : List FactorBlock).map factorBlockValue).prod) = 349996873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_767537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 349996873) ^ 174998436 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 116665624 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 18420888 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 456 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_362051087 : Nat.Prime 362051087 := by
  apply lucas_primality 362051087 (5 : ZMod 362051087)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) = 362051087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_12539
      · exact prime_oneHundredThirtyDX_14437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 362051087) ^ 181025543 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 28874 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 25078 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_388344499 : Nat.Prime 388344499 := by
  apply lucas_primality 388344499 (2 : ZMod 388344499)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (727, 1), (5237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (727, 1), (5237, 1)] : List FactorBlock).map factorBlockValue).prod) = 388344499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_727
      · exact prime_oneHundredThirtyDX_5237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 388344499) ^ 194172249 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 388344499) ^ 129448166 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 388344499) ^ 22843794 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 388344499) ^ 534174 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 388344499) ^ 74154 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_429543953 : Nat.Prime 429543953 := by
  apply lucas_primality 429543953 (3 : ZMod 429543953)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (37, 1), (31547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (37, 1), (31547, 1)] : List FactorBlock).map factorBlockValue).prod) = 429543953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_23
      · exact prime_oneHundredThirtyDX_37
      · exact prime_oneHundredThirtyDX_31547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 429543953) ^ 214771976 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 18675824 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 11609296 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 13616 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_450338671 : Nat.Prime 450338671 := by
  apply lucas_primality 450338671 (3 : ZMod 450338671)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (17, 1), (41, 1), (2393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (17, 1), (41, 1), (2393, 1)] : List FactorBlock).map factorBlockValue).prod) = 450338671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_41
      · exact prime_oneHundredThirtyDX_2393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 450338671) ^ 225169335 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 450338671) ^ 150112890 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 450338671) ^ 90067734 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 450338671) ^ 26490510 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 450338671) ^ 10983870 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 450338671) ^ 188190 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_492488791 : Nat.Prime 492488791 := by
  apply lucas_primality 492488791 (7 : ZMod 492488791)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (16416293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (16416293, 1)] : List FactorBlock).map factorBlockValue).prod) = 492488791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_16416293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 492488791) ^ 246244395 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 492488791) ^ 164162930 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 492488791) ^ 98497758 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 492488791) ^ 30 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_552388373 : Nat.Prime 552388373 := by
  apply lucas_primality 552388373 (2 : ZMod 552388373)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (653, 1), (2897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (653, 1), (2897, 1)] : List FactorBlock).map factorBlockValue).prod) = 552388373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_73
      · exact prime_oneHundredThirtyDX_653
      · exact prime_oneHundredThirtyDX_2897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 552388373) ^ 276194186 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 552388373) ^ 7566964 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 552388373) ^ 845924 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 552388373) ^ 190676 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_644572237 : Nat.Prime 644572237 := by
  apply lucas_primality 644572237 (2 : ZMod 644572237)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (43, 1), (16223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (43, 1), (16223, 1)] : List FactorBlock).map factorBlockValue).prod) = 644572237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_43
      · exact prime_oneHundredThirtyDX_16223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 644572237) ^ 322286118 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 644572237) ^ 214857412 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 644572237) ^ 92081748 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 644572237) ^ 58597476 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 644572237) ^ 14990052 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 644572237) ^ 39732 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_647419757 : Nat.Prime 647419757 := by
  apply lucas_primality 647419757 (2 : ZMod 647419757)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (8518681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (8518681, 1)] : List FactorBlock).map factorBlockValue).prod) = 647419757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_8518681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 647419757) ^ 323709878 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 647419757) ^ 34074724 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 647419757) ^ 76 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_17203
      · exact prime_oneHundredThirtyDX_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_729682649 : Nat.Prime 729682649 := by
  apply lucas_primality 729682649 (3 : ZMod 729682649)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (107, 1), (191, 1), (4463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (107, 1), (191, 1), (4463, 1)] : List FactorBlock).map factorBlockValue).prod) = 729682649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_107
      · exact prime_oneHundredThirtyDX_191
      · exact prime_oneHundredThirtyDX_4463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 729682649) ^ 364841324 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 729682649) ^ 6819464 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 729682649) ^ 3820328 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 729682649) ^ 163496 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_806303317 : Nat.Prime 806303317 := by
  apply lucas_primality 806303317 (5 : ZMod 806303317)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (738373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (738373, 1)] : List FactorBlock).map factorBlockValue).prod) = 806303317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_738373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 806303317) ^ 403151658 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 806303317) ^ 268767772 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 806303317) ^ 115186188 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 806303317) ^ 62023332 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 806303317) ^ 1092 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_820351907 : Nat.Prime 820351907 := by
  apply lucas_primality 820351907 (2 : ZMod 820351907)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (37288723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (37288723, 1)] : List FactorBlock).map factorBlockValue).prod) = 820351907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_37288723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 820351907) ^ 410175953 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 820351907) ^ 74577446 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 820351907) ^ 22 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_938742491 : Nat.Prime 938742491 := by
  apply lucas_primality 938742491 (2 : ZMod 938742491)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (751, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (751, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) = 938742491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_751
      · exact prime_oneHundredThirtyDX_2551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 938742491) ^ 469371245 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 938742491) ^ 187748498 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 938742491) ^ 134106070 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 938742491) ^ 1249990 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 938742491) ^ 367990 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1036932751 : Nat.Prime 1036932751 := by
  apply lucas_primality 1036932751 (6 : ZMod 1036932751)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 3), (7, 1), (65837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 3), (7, 1), (65837, 1)] : List FactorBlock).map factorBlockValue).prod) = 1036932751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_65837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1036932751) ^ 518466375 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1036932751) ^ 345644250 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1036932751) ^ 207386550 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1036932751) ^ 148133250 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1036932751) ^ 15750 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1243852667 : Nat.Prime 1243852667 := by
  apply lucas_primality 1243852667 (2 : ZMod 1243852667)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (88846619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (88846619, 1)] : List FactorBlock).map factorBlockValue).prod) = 1243852667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_88846619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1243852667) ^ 621926333 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1243852667) ^ 177693238 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1243852667) ^ 14 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1298878813 : Nat.Prime 1298878813 := by
  apply lucas_primality 1298878813 (2 : ZMod 1298878813)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (11, 1), (17, 1), (43, 1), (641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (11, 1), (17, 1), (43, 1), (641, 1)] : List FactorBlock).map factorBlockValue).prod) = 1298878813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_43
      · exact prime_oneHundredThirtyDX_641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1298878813) ^ 649439406 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1298878813) ^ 432959604 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1298878813) ^ 185554116 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1298878813) ^ 118079892 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1298878813) ^ 76404636 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1298878813) ^ 30206484 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1298878813) ^ 2026332 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1335625751 : Nat.Prime 1335625751 := by
  apply lucas_primality 1335625751 (11 : ZMod 1335625751)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (5342503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (5342503, 1)] : List FactorBlock).map factorBlockValue).prod) = 1335625751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_5342503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1335625751) ^ 667812875 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 1335625751) ^ 267125150 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 1335625751) ^ 250 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1614799441 : Nat.Prime 1614799441 := by
  apply lucas_primality 1614799441 (7 : ZMod 1614799441)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (2242777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (2242777, 1)] : List FactorBlock).map factorBlockValue).prod) = 1614799441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_2242777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1614799441) ^ 807399720 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1614799441) ^ 538266480 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1614799441) ^ 322959888 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1614799441) ^ 720 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1697662997 : Nat.Prime 1697662997 := by
  apply lucas_primality 1697662997 (2 : ZMod 1697662997)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (22337671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (22337671, 1)] : List FactorBlock).map factorBlockValue).prod) = 1697662997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_22337671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1697662997) ^ 848831498 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1697662997) ^ 89350684 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1697662997) ^ 76 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1765858093 : Nat.Prime 1765858093 := by
  apply lucas_primality 1765858093 (5 : ZMod 1765858093)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (241, 1), (373, 1), (1637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (241, 1), (373, 1), (1637, 1)] : List FactorBlock).map factorBlockValue).prod) = 1765858093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_241
      · exact prime_oneHundredThirtyDX_373
      · exact prime_oneHundredThirtyDX_1637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1765858093) ^ 882929046 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1765858093) ^ 588619364 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1765858093) ^ 7327212 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1765858093) ^ 4734204 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1765858093) ^ 1078716 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2020103153 : Nat.Prime 2020103153 := by
  apply lucas_primality 2020103153 (3 : ZMod 2020103153)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (126256447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (126256447, 1)] : List FactorBlock).map factorBlockValue).prod) = 2020103153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_126256447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2020103153) ^ 1010051576 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2020103153) ^ 16 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2318099881 : Nat.Prime 2318099881 := by
  apply lucas_primality 2318099881 (7 : ZMod 2318099881)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (349, 1), (55351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (349, 1), (55351, 1)] : List FactorBlock).map factorBlockValue).prod) = 2318099881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_349
      · exact prime_oneHundredThirtyDX_55351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2318099881) ^ 1159049940 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 772699960 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 463619976 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 6642120 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 41880 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2342057833 : Nat.Prime 2342057833 := by
  apply lucas_primality 2342057833 (5 : ZMod 2342057833)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (73, 1), (445597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (73, 1), (445597, 1)] : List FactorBlock).map factorBlockValue).prod) = 2342057833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_73
      · exact prime_oneHundredThirtyDX_445597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2342057833) ^ 1171028916 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 2342057833) ^ 780685944 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 2342057833) ^ 32082984 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 2342057833) ^ 5256 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2659183601 : Nat.Prime 2659183601 := by
  apply lucas_primality 2659183601 (3 : ZMod 2659183601)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (6647959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (6647959, 1)] : List FactorBlock).map factorBlockValue).prod) = 2659183601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_6647959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2659183601) ^ 1329591800 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2659183601) ^ 531836720 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2659183601) ^ 400 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2719402627 : Nat.Prime 2719402627 := by
  apply lucas_primality 2719402627 (2 : ZMod 2719402627)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (277, 1), (86117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (277, 1), (86117, 1)] : List FactorBlock).map factorBlockValue).prod) = 2719402627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_277
      · exact prime_oneHundredThirtyDX_86117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2719402627) ^ 1359701313 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2719402627) ^ 906467542 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2719402627) ^ 143126454 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2719402627) ^ 9817338 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2719402627) ^ 31578 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2924270879 : Nat.Prime 2924270879 := by
  apply lucas_primality 2924270879 (23 : ZMod 2924270879)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (67, 1), (1283701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (67, 1), (1283701, 1)] : List FactorBlock).map factorBlockValue).prod) = 2924270879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_67
      · exact prime_oneHundredThirtyDX_1283701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 2924270879) ^ 1462135439 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (23 : ZMod 2924270879) ^ 172015934 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (23 : ZMod 2924270879) ^ 43645834 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (23 : ZMod 2924270879) ^ 2278 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_3119242051 : Nat.Prime 3119242051 := by
  apply lucas_primality 3119242051 (3 : ZMod 3119242051)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (6931649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (6931649, 1)] : List FactorBlock).map factorBlockValue).prod) = 3119242051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_6931649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3119242051) ^ 1559621025 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3119242051) ^ 1039747350 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3119242051) ^ 623848410 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3119242051) ^ 450 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_3578999597 : Nat.Prime 3578999597 := by
  apply lucas_primality 3578999597 (2 : ZMod 3578999597)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (6863, 1), (7669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (6863, 1), (7669, 1)] : List FactorBlock).map factorBlockValue).prod) = 3578999597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_6863
      · exact prime_oneHundredThirtyDX_7669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3578999597) ^ 1789499798 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3578999597) ^ 210529388 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3578999597) ^ 521492 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3578999597) ^ 466684 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_3658717009 : Nat.Prime 3658717009 := by
  apply lucas_primality 3658717009 (14 : ZMod 3658717009)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (25407757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (25407757, 1)] : List FactorBlock).map factorBlockValue).prod) = 3658717009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_25407757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 3658717009) ^ 1829358504 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (14 : ZMod 3658717009) ^ 1219572336 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (14 : ZMod 3658717009) ^ 144 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_4171314503 : Nat.Prime 4171314503 := by
  apply lucas_primality 4171314503 (5 : ZMod 4171314503)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (48503657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (48503657, 1)] : List FactorBlock).map factorBlockValue).prod) = 4171314503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_43
      · exact prime_oneHundredThirtyDX_48503657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4171314503) ^ 2085657251 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 4171314503) ^ 97007314 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 4171314503) ^ 86 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_4503386711 : Nat.Prime 4503386711 := by
  apply lucas_primality 4503386711 (13 : ZMod 4503386711)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (450338671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (450338671, 1)] : List FactorBlock).map factorBlockValue).prod) = 4503386711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_450338671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 4503386711) ^ 2251693355 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 4503386711) ^ 900677342 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 4503386711) ^ 10 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_4717239199 : Nat.Prime 4717239199 := by
  apply lucas_primality 4717239199 (6 : ZMod 4717239199)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (112315219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (112315219, 1)] : List FactorBlock).map factorBlockValue).prod) = 4717239199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_112315219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 4717239199) ^ 2358619599 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 4717239199) ^ 1572413066 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 4717239199) ^ 673891314 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 4717239199) ^ 42 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_5848541759 : Nat.Prime 5848541759 := by
  apply lucas_primality 5848541759 (7 : ZMod 5848541759)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2924270879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2924270879, 1)] : List FactorBlock).map factorBlockValue).prod) = 5848541759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_2924270879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 5848541759) ^ 2924270879 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 5848541759) ^ 2 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_31
      · exact prime_oneHundredThirtyDX_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_6383555873 : Nat.Prime 6383555873 := by
  apply lucas_primality 6383555873 (3 : ZMod 6383555873)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (199486121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (199486121, 1)] : List FactorBlock).map factorBlockValue).prod) = 6383555873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_199486121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 6383555873) ^ 3191777936 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6383555873) ^ 32 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_6998309863 : Nat.Prime 6998309863 := by
  apply lucas_primality 6998309863 (3 : ZMod 6998309863)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (19, 1), (67, 1), (53897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (19, 1), (67, 1), (53897, 1)] : List FactorBlock).map factorBlockValue).prod) = 6998309863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_67
      · exact prime_oneHundredThirtyDX_53897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6998309863) ^ 3499154931 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 2332769954 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 411665286 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 368332098 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 104452386 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 129846 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_8747821997 : Nat.Prime 8747821997 := by
  apply lucas_primality 8747821997 (2 : ZMod 8747821997)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (79, 1), (151, 1), (9649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (79, 1), (151, 1), (9649, 1)] : List FactorBlock).map factorBlockValue).prod) = 8747821997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_79
      · exact prime_oneHundredThirtyDX_151
      · exact prime_oneHundredThirtyDX_9649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8747821997) ^ 4373910998 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8747821997) ^ 460411684 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8747821997) ^ 110731924 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8747821997) ^ 57932596 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8747821997) ^ 906604 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_9257508937 : Nat.Prime 9257508937 := by
  apply lucas_primality 9257508937 (5 : ZMod 9257508937)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (9890501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (9890501, 1)] : List FactorBlock).map factorBlockValue).prod) = 9257508937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_9890501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9257508937) ^ 4628754468 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 3085836312 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 712116072 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 936 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_9568542161 : Nat.Prime 9568542161 := by
  apply lucas_primality 9568542161 (3 : ZMod 9568542161)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (73, 1), (197, 1), (8317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (73, 1), (197, 1), (8317, 1)] : List FactorBlock).map factorBlockValue).prod) = 9568542161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_73
      · exact prime_oneHundredThirtyDX_197
      · exact prime_oneHundredThirtyDX_8317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9568542161) ^ 4784271080 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9568542161) ^ 1913708432 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9568542161) ^ 131075920 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9568542161) ^ 48571280 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9568542161) ^ 1150480 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_11077808851 : Nat.Prime 11077808851 := by
  apply lucas_primality 11077808851 (3 : ZMod 11077808851)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (2267, 1), (10859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (2267, 1), (10859, 1)] : List FactorBlock).map factorBlockValue).prod) = 11077808851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_2267
      · exact prime_oneHundredThirtyDX_10859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11077808851) ^ 5538904425 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 11077808851) ^ 3692602950 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 11077808851) ^ 2215561770 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 11077808851) ^ 4886550 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 11077808851) ^ 1020150 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_12886318591 : Nat.Prime 12886318591 := by
  apply lucas_primality 12886318591 (6 : ZMod 12886318591)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (429543953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (429543953, 1)] : List FactorBlock).map factorBlockValue).prod) = 12886318591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_429543953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 12886318591) ^ 6443159295 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 4295439530 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 2577263718 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 30 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_13944876047 : Nat.Prime 13944876047 := by
  apply lucas_primality 13944876047 (5 : ZMod 13944876047)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (199, 1), (35037377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (199, 1), (35037377, 1)] : List FactorBlock).map factorBlockValue).prod) = 13944876047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_199
      · exact prime_oneHundredThirtyDX_35037377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 13944876047) ^ 6972438023 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 13944876047) ^ 70074754 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 13944876047) ^ 398 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_14750067271 : Nat.Prime 14750067271 := by
  apply lucas_primality 14750067271 (15 : ZMod 14750067271)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (101, 1), (256211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (101, 1), (256211, 1)] : List FactorBlock).map factorBlockValue).prod) = 14750067271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_101
      · exact prime_oneHundredThirtyDX_256211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 14750067271) ^ 7375033635 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (15 : ZMod 14750067271) ^ 4916689090 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (15 : ZMod 14750067271) ^ 2950013454 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (15 : ZMod 14750067271) ^ 776319330 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (15 : ZMod 14750067271) ^ 146040270 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (15 : ZMod 14750067271) ^ 57570 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_16514973161 : Nat.Prime 16514973161 := by
  apply lucas_primality 16514973161 (3 : ZMod 16514973161)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (349, 1), (169003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (349, 1), (169003, 1)] : List FactorBlock).map factorBlockValue).prod) = 16514973161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_349
      · exact prime_oneHundredThirtyDX_169003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16514973161) ^ 8257486580 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 16514973161) ^ 3302994632 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 16514973161) ^ 2359281880 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 16514973161) ^ 47320840 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 16514973161) ^ 97720 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_16878357739 : Nat.Prime 16878357739 := by
  apply lucas_primality 16878357739 (3 : ZMod 16878357739)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (3607, 1), (23633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (3607, 1), (23633, 1)] : List FactorBlock).map factorBlockValue).prod) = 16878357739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_3607
      · exact prime_oneHundredThirtyDX_23633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16878357739) ^ 8439178869 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 16878357739) ^ 5626119246 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 16878357739) ^ 1534396158 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 16878357739) ^ 4679334 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 16878357739) ^ 714186 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_18937205509 : Nat.Prime 18937205509 := by
  apply lucas_primality 18937205509 (7 : ZMod 18937205509)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (3347, 1), (36269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (3347, 1), (36269, 1)] : List FactorBlock).map factorBlockValue).prod) = 18937205509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_3347
      · exact prime_oneHundredThirtyDX_36269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 18937205509) ^ 9468602754 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 18937205509) ^ 6312401836 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 18937205509) ^ 1456708116 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 18937205509) ^ 5657964 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 18937205509) ^ 522132 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_21036514813 : Nat.Prime 21036514813 := by
  apply lucas_primality 21036514813 (5 : ZMod 21036514813)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (3727, 1), (15173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (3727, 1), (15173, 1)] : List FactorBlock).map factorBlockValue).prod) = 21036514813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_31
      · exact prime_oneHundredThirtyDX_3727
      · exact prime_oneHundredThirtyDX_15173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21036514813) ^ 10518257406 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 21036514813) ^ 7012171604 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 21036514813) ^ 678597252 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 21036514813) ^ 5644356 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 21036514813) ^ 1386444 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_21473997583 : Nat.Prime 21473997583 := by
  apply lucas_primality 21473997583 (3 : ZMod 21473997583)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3578999597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3578999597, 1)] : List FactorBlock).map factorBlockValue).prod) = 21473997583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_3578999597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 21473997583) ^ 10736998791 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 21473997583) ^ 7157999194 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 21473997583) ^ 6 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_22223881153 : Nat.Prime 22223881153 := by
  apply lucas_primality 22223881153 (5 : ZMod 22223881153)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (11, 1), (31, 1), (113147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (11, 1), (31, 1), (113147, 1)] : List FactorBlock).map factorBlockValue).prod) = 22223881153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_31
      · exact prime_oneHundredThirtyDX_113147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 22223881153) ^ 11111940576 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 22223881153) ^ 7407960384 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 22223881153) ^ 2020352832 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 22223881153) ^ 716899392 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 22223881153) ^ 196416 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_22292713759 : Nat.Prime 22292713759 := by
  apply lucas_primality 22292713759 (7 : ZMod 22292713759)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (75825557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (75825557, 1)] : List FactorBlock).map factorBlockValue).prod) = 22292713759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_75825557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 22292713759) ^ 11146356879 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 22292713759) ^ 7430904586 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 22292713759) ^ 3184673394 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 22292713759) ^ 294 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_23096547757 : Nat.Prime 23096547757 := by
  apply lucas_primality 23096547757 (5 : ZMod 23096547757)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (79, 1), (163, 1), (49823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (79, 1), (163, 1), (49823, 1)] : List FactorBlock).map factorBlockValue).prod) = 23096547757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_79
      · exact prime_oneHundredThirtyDX_163
      · exact prime_oneHundredThirtyDX_49823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 23096547757) ^ 11548273878 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 7698849252 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 292361364 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 141696612 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 463572 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_24826405999 : Nat.Prime 24826405999 := by
  apply lucas_primality 24826405999 (6 : ZMod 24826405999)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (46491397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (46491397, 1)] : List FactorBlock).map factorBlockValue).prod) = 24826405999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_89
      · exact prime_oneHundredThirtyDX_46491397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 24826405999) ^ 12413202999 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 24826405999) ^ 8275468666 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 24826405999) ^ 278948382 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 24826405999) ^ 534 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_24944535739 : Nat.Prime 24944535739 := by
  apply lucas_primality 24944535739 (2 : ZMod 24944535739)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 1), (24312413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 1), (24312413, 1)] : List FactorBlock).map factorBlockValue).prod) = 24944535739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_24312413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24944535739) ^ 12472267869 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24944535739) ^ 8314845246 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24944535739) ^ 1312870302 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24944535739) ^ 1026 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_26702345737 : Nat.Prime 26702345737 := by
  apply lucas_primality 26702345737 (5 : ZMod 26702345737)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (11, 1), (163, 1), (68947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (11, 1), (163, 1), (68947, 1)] : List FactorBlock).map factorBlockValue).prod) = 26702345737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_163
      · exact prime_oneHundredThirtyDX_68947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 26702345737) ^ 13351172868 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 26702345737) ^ 8900781912 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 26702345737) ^ 2427485976 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 26702345737) ^ 163818072 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 26702345737) ^ 387288 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_26896283387 : Nat.Prime 26896283387 := by
  apply lucas_primality 26896283387 (2 : ZMod 26896283387)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (51923327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (51923327, 1)] : List FactorBlock).map factorBlockValue).prod) = 26896283387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_37
      · exact prime_oneHundredThirtyDX_51923327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26896283387) ^ 13448141693 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 26896283387) ^ 3842326198 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 26896283387) ^ 726926578 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 26896283387) ^ 518 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_34432049579 : Nat.Prime 34432049579 := by
  apply lucas_primality 34432049579 (2 : ZMod 34432049579)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (853, 1), (20182913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (853, 1), (20182913, 1)] : List FactorBlock).map factorBlockValue).prod) = 34432049579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_853
      · exact prime_oneHundredThirtyDX_20182913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 34432049579) ^ 17216024789 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34432049579) ^ 40365826 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34432049579) ^ 1706 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_34671681157 : Nat.Prime 34671681157 := by
  apply lucas_primality 34671681157 (2 : ZMod 34671681157)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (19, 1), (21724111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (19, 1), (21724111, 1)] : List FactorBlock).map factorBlockValue).prod) = 34671681157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_21724111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34671681157) ^ 17335840578 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34671681157) ^ 11557227052 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34671681157) ^ 4953097308 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34671681157) ^ 1824825324 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34671681157) ^ 1596 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_43510442033 : Nat.Prime 43510442033 := by
  apply lucas_primality 43510442033 (3 : ZMod 43510442033)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2719402627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2719402627, 1)] : List FactorBlock).map factorBlockValue).prod) = 43510442033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_2719402627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 43510442033) ^ 21755221016 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 43510442033) ^ 16 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_53183672021 : Nat.Prime 53183672021 := by
  apply lucas_primality 53183672021 (2 : ZMod 53183672021)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2659183601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2659183601, 1)] : List FactorBlock).map factorBlockValue).prod) = 53183672021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_2659183601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 53183672021) ^ 26591836010 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 53183672021) ^ 10636734404 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 53183672021) ^ 20 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_65207015611 : Nat.Prime 65207015611 := by
  apply lucas_primality 65207015611 (10 : ZMod 65207015611)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (10399843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (10399843, 1)] : List FactorBlock).map factorBlockValue).prod) = 65207015611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_10399843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 65207015611) ^ 32603507805 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (10 : ZMod 65207015611) ^ 21735671870 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (10 : ZMod 65207015611) ^ 13041403122 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (10 : ZMod 65207015611) ^ 5927910510 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (10 : ZMod 65207015611) ^ 3431948190 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (10 : ZMod 65207015611) ^ 6270 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_65960035991 : Nat.Prime 65960035991 := by
  apply lucas_primality 65960035991 (11 : ZMod 65960035991)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2999, 1), (2199401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2999, 1), (2199401, 1)] : List FactorBlock).map factorBlockValue).prod) = 65960035991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_2999
      · exact prime_oneHundredThirtyDX_2199401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 65960035991) ^ 32980017995 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 65960035991) ^ 13192007198 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 65960035991) ^ 21994010 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 65960035991) ^ 29990 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_68864099159 : Nat.Prime 68864099159 := by
  apply lucas_primality 68864099159 (7 : ZMod 68864099159)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (34432049579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (34432049579, 1)] : List FactorBlock).map factorBlockValue).prod) = 68864099159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_34432049579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 68864099159) ^ 34432049579 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 68864099159) ^ 2 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_70936967429 : Nat.Prime 70936967429 := by
  apply lucas_primality 70936967429 (2 : ZMod 70936967429)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17341, 1), (1022677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17341, 1), (1022677, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936967429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_17341
      · exact prime_oneHundredThirtyDX_1022677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 70936967429) ^ 35468483714 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 70936967429) ^ 4090708 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 70936967429) ^ 69364 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_74775919583 : Nat.Prime 74775919583 := by
  apply lucas_primality 74775919583 (5 : ZMod 74775919583)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (43, 1), (9554807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (43, 1), (9554807, 1)] : List FactorBlock).map factorBlockValue).prod) = 74775919583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_43
      · exact prime_oneHundredThirtyDX_9554807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 74775919583) ^ 37387959791 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 10682274226 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 5751993814 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 1738974874 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 7826 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_74913664993 : Nat.Prime 74913664993 := by
  apply lucas_primality 74913664993 (5 : ZMod 74913664993)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (45902981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (45902981, 1)] : List FactorBlock).map factorBlockValue).prod) = 74913664993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_45902981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 74913664993) ^ 37456832496 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 74913664993) ^ 24971221664 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 74913664993) ^ 4406686176 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 74913664993) ^ 1632 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_88787940239 : Nat.Prime 88787940239 := by
  apply lucas_primality 88787940239 (11 : ZMod 88787940239)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (41, 1), (107, 1), (595261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (41, 1), (107, 1), (595261, 1)] : List FactorBlock).map factorBlockValue).prod) = 88787940239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_41
      · exact prime_oneHundredThirtyDX_107
      · exact prime_oneHundredThirtyDX_595261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 88787940239) ^ 44393970119 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 88787940239) ^ 5222820014 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 88787940239) ^ 2165559518 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 88787940239) ^ 829793834 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 88787940239) ^ 149158 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_105036043537 : Nat.Prime 105036043537 := by
  apply lucas_primality 105036043537 (7 : ZMod 105036043537)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (2381, 1), (306349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (2381, 1), (306349, 1)] : List FactorBlock).map factorBlockValue).prod) = 105036043537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_2381
      · exact prime_oneHundredThirtyDX_306349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 105036043537) ^ 52518021768 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 105036043537) ^ 35012014512 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 105036043537) ^ 44114256 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 105036043537) ^ 342864 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_109117019597 : Nat.Prime 109117019597 := by
  apply lucas_primality 109117019597 (2 : ZMod 109117019597)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (9721, 1), (215863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (9721, 1), (215863, 1)] : List FactorBlock).map factorBlockValue).prod) = 109117019597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_9721
      · exact prime_oneHundredThirtyDX_215863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 109117019597) ^ 54558509798 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 109117019597) ^ 8393616892 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 109117019597) ^ 11224876 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 109117019597) ^ 505492 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_110778088511 : Nat.Prime 110778088511 := by
  apply lucas_primality 110778088511 (17 : ZMod 110778088511)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11077808851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11077808851, 1)] : List FactorBlock).map factorBlockValue).prod) = 110778088511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_11077808851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 110778088511) ^ 55389044255 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (17 : ZMod 110778088511) ^ 22155617702 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (17 : ZMod 110778088511) ^ 10 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_118662433481 : Nat.Prime 118662433481 := by
  apply lucas_primality 118662433481 (6 : ZMod 118662433481)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (71, 1), (79, 1), (263, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (71, 1), (79, 1), (263, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) = 118662433481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_71
      · exact prime_oneHundredThirtyDX_79
      · exact prime_oneHundredThirtyDX_263
      · exact prime_oneHundredThirtyDX_2011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 118662433481) ^ 59331216740 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 23732486696 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 1671301880 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 1502056120 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 451187960 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 59006680 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_137728198319 : Nat.Prime 137728198319 := by
  apply lucas_primality 137728198319 (17 : ZMod 137728198319)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (68864099159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (68864099159, 1)] : List FactorBlock).map factorBlockValue).prod) = 137728198319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_68864099159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (17 : ZMod 137728198319) ^ 68864099159 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (17 : ZMod 137728198319) ^ 2 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_140168308879 : Nat.Prime 140168308879 := by
  apply lucas_primality 140168308879 (3 : ZMod 140168308879)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) = 140168308879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_853
      · exact prime_oneHundredThirtyDX_702239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 140168308879) ^ 70084154439 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 46722769626 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 10782177606 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 164323926 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 199602 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_141861363151 : Nat.Prime 141861363151 := by
  apply lucas_primality 141861363151 (12 : ZMod 141861363151)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (13, 2), (83, 1), (191, 1), (353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (13, 2), (83, 1), (191, 1), (353, 1)] : List FactorBlock).map factorBlockValue).prod) = 141861363151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_83
      · exact prime_oneHundredThirtyDX_191
      · exact prime_oneHundredThirtyDX_353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 141861363151) ^ 70930681575 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (12 : ZMod 141861363151) ^ 47287121050 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (12 : ZMod 141861363151) ^ 28372272630 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (12 : ZMod 141861363151) ^ 10912412550 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (12 : ZMod 141861363151) ^ 1709173050 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (12 : ZMod 141861363151) ^ 742729650 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (12 : ZMod 141861363151) ^ 401873550 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_252438177757 : Nat.Prime 252438177757 := by
  apply lucas_primality 252438177757 (5 : ZMod 252438177757)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (21036514813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (21036514813, 1)] : List FactorBlock).map factorBlockValue).prod) = 252438177757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_21036514813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 252438177757) ^ 126219088878 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 252438177757) ^ 84146059252 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 252438177757) ^ 12 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_267597212401 : Nat.Prime 267597212401 := by
  apply lucas_primality 267597212401 (33 : ZMod 267597212401)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (7, 4), (83, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (7, 4), (83, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) = 267597212401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_83
      · exact prime_oneHundredThirtyDX_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (33 : ZMod 267597212401) ^ 133798606200 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (33 : ZMod 267597212401) ^ 89199070800 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (33 : ZMod 267597212401) ^ 53519442480 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (33 : ZMod 267597212401) ^ 38228173200 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (33 : ZMod 267597212401) ^ 3224062800 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (33 : ZMod 267597212401) ^ 717418800 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_275384832181 : Nat.Prime 275384832181 := by
  apply lucas_primality 275384832181 (2 : ZMod 275384832181)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (3181, 1), (1442863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (3181, 1), (1442863, 1)] : List FactorBlock).map factorBlockValue).prod) = 275384832181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_3181
      · exact prime_oneHundredThirtyDX_1442863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 275384832181) ^ 137692416090 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 275384832181) ^ 91794944060 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 275384832181) ^ 55076966436 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 275384832181) ^ 86571780 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 275384832181) ^ 190860 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_276114607397 : Nat.Prime 276114607397 := by
  apply lucas_primality 276114607397 (2 : ZMod 276114607397)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (557, 1), (1301, 1), (95257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (557, 1), (1301, 1), (95257, 1)] : List FactorBlock).map factorBlockValue).prod) = 276114607397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_557
      · exact prime_oneHundredThirtyDX_1301
      · exact prime_oneHundredThirtyDX_95257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 276114607397) ^ 138057303698 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 276114607397) ^ 495717428 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 276114607397) ^ 212232596 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 276114607397) ^ 2898628 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_358753473289 : Nat.Prime 358753473289 := by
  apply lucas_primality 358753473289 (17 : ZMod 358753473289)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (19, 1), (431, 1), (86923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (19, 1), (431, 1), (86923, 1)] : List FactorBlock).map factorBlockValue).prod) = 358753473289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_431
      · exact prime_oneHundredThirtyDX_86923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 358753473289) ^ 179376736644 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (17 : ZMod 358753473289) ^ 119584491096 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (17 : ZMod 358753473289) ^ 51250496184 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (17 : ZMod 358753473289) ^ 18881761752 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (17 : ZMod 358753473289) ^ 832374648 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (17 : ZMod 358753473289) ^ 4127256 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_362765197849 : Nat.Prime 362765197849 := by
  apply lucas_primality 362765197849 (7 : ZMod 362765197849)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (757, 1), (19967261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (757, 1), (19967261, 1)] : List FactorBlock).map factorBlockValue).prod) = 362765197849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_757
      · exact prime_oneHundredThirtyDX_19967261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 362765197849) ^ 181382598924 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 362765197849) ^ 120921732616 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 362765197849) ^ 479214264 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 362765197849) ^ 18168 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_396131785997 : Nat.Prime 396131785997 := by
  apply lucas_primality 396131785997 (2 : ZMod 396131785997)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (21881, 1), (32561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (21881, 1), (32561, 1)] : List FactorBlock).map factorBlockValue).prod) = 396131785997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_139
      · exact prime_oneHundredThirtyDX_21881
      · exact prime_oneHundredThirtyDX_32561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 396131785997) ^ 198065892998 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 396131785997) ^ 2849868964 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 396131785997) ^ 18103916 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 396131785997) ^ 12165836 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_498898911439 : Nat.Prime 498898911439 := by
  apply lucas_primality 498898911439 (3 : ZMod 498898911439)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (43, 1), (644572237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (43, 1), (644572237, 1)] : List FactorBlock).map factorBlockValue).prod) = 498898911439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_43
      · exact prime_oneHundredThirtyDX_644572237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 498898911439) ^ 249449455719 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 498898911439) ^ 166299637146 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 498898911439) ^ 11602300266 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 498898911439) ^ 774 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_592712155459 : Nat.Prime 592712155459 := by
  apply lucas_primality 592712155459 (2 : ZMod 592712155459)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (3658717009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (3658717009, 1)] : List FactorBlock).map factorBlockValue).prod) = 592712155459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_3658717009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 592712155459) ^ 296356077729 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 592712155459) ^ 197570718486 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 592712155459) ^ 162 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_762831713857 : Nat.Prime 762831713857 := by
  apply lucas_primality 762831713857 (5 : ZMod 762831713857)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (67, 1), (127, 1), (173, 1), (2699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (67, 1), (127, 1), (173, 1), (2699, 1)] : List FactorBlock).map factorBlockValue).prod) = 762831713857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_67
      · exact prime_oneHundredThirtyDX_127
      · exact prime_oneHundredThirtyDX_173
      · exact prime_oneHundredThirtyDX_2699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 762831713857) ^ 381415856928 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 762831713857) ^ 254277237952 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 762831713857) ^ 11385547968 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 762831713857) ^ 6006548928 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 762831713857) ^ 4409431872 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 762831713857) ^ 282634944 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_944154591371 : Nat.Prime 944154591371 := by
  apply lucas_primality 944154591371 (2 : ZMod 944154591371)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (439, 1), (215069383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (439, 1), (215069383, 1)] : List FactorBlock).map factorBlockValue).prod) = 944154591371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_439
      · exact prime_oneHundredThirtyDX_215069383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 944154591371) ^ 472077295685 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 944154591371) ^ 188830918274 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 944154591371) ^ 2150693830 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 944154591371) ^ 4390 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1006118489359 : Nat.Prime 1006118489359 := by
  apply lucas_primality 1006118489359 (3 : ZMod 1006118489359)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (23, 1), (2003, 1), (4993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (23, 1), (2003, 1), (4993, 1)] : List FactorBlock).map factorBlockValue).prod) = 1006118489359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_23
      · exact prime_oneHundredThirtyDX_2003
      · exact prime_oneHundredThirtyDX_4993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1006118489359) ^ 503059244679 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1006118489359) ^ 335372829786 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1006118489359) ^ 43744282146 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1006118489359) ^ 502305786 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1006118489359) ^ 201505806 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1022058768707 : Nat.Prime 1022058768707 := by
  apply lucas_primality 1022058768707 (2 : ZMod 1022058768707)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (26896283387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (26896283387, 1)] : List FactorBlock).map factorBlockValue).prod) = 1022058768707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_26896283387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1022058768707) ^ 511029384353 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1022058768707) ^ 53792566774 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1022058768707) ^ 38 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1101825586553 : Nat.Prime 1101825586553 := by
  apply lucas_primality 1101825586553 (3 : ZMod 1101825586553)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (137728198319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (137728198319, 1)] : List FactorBlock).map factorBlockValue).prod) = 1101825586553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_137728198319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1101825586553) ^ 550912793276 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1101825586553) ^ 8 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1145456805431 : Nat.Prime 1145456805431 := by
  apply lucas_primality 1145456805431 (7 : ZMod 1145456805431)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (251, 1), (2103029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (251, 1), (2103029, 1)] : List FactorBlock).map factorBlockValue).prod) = 1145456805431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_31
      · exact prime_oneHundredThirtyDX_251
      · exact prime_oneHundredThirtyDX_2103029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1145456805431) ^ 572728402715 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1145456805431) ^ 229091361086 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1145456805431) ^ 163636686490 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1145456805431) ^ 36950219530 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1145456805431) ^ 4563572930 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1145456805431) ^ 544670 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1367652133241 : Nat.Prime 1367652133241 := by
  apply lucas_primality 1367652133241 (3 : ZMod 1367652133241)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (541, 1), (63200191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (541, 1), (63200191, 1)] : List FactorBlock).map factorBlockValue).prod) = 1367652133241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_541
      · exact prime_oneHundredThirtyDX_63200191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1367652133241) ^ 683826066620 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1367652133241) ^ 273530426648 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1367652133241) ^ 2528007640 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1367652133241) ^ 21640 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1506989404211 : Nat.Prime 1506989404211 := by
  apply lucas_primality 1506989404211 (6 : ZMod 1506989404211)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (131, 1), (139, 1), (271, 1), (30539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (131, 1), (139, 1), (271, 1), (30539, 1)] : List FactorBlock).map factorBlockValue).prod) = 1506989404211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_131
      · exact prime_oneHundredThirtyDX_139
      · exact prime_oneHundredThirtyDX_271
      · exact prime_oneHundredThirtyDX_30539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1506989404211) ^ 753494702105 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1506989404211) ^ 301397880842 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1506989404211) ^ 11503735910 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1506989404211) ^ 10841650390 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1506989404211) ^ 5560846510 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1506989404211) ^ 49346390 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1564506913061 : Nat.Prime 1564506913061 := by
  apply lucas_primality 1564506913061 (2 : ZMod 1564506913061)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (281, 1), (3059143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (281, 1), (3059143, 1)] : List FactorBlock).map factorBlockValue).prod) = 1564506913061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_281
      · exact prime_oneHundredThirtyDX_3059143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1564506913061) ^ 782253456530 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 312901382612 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 223500987580 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 120346685620 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 5567640260 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 511420 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1623791970233 : Nat.Prime 1623791970233 := by
  apply lucas_primality 1623791970233 (3 : ZMod 1623791970233)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (53, 1), (39679, 1), (96517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (53, 1), (39679, 1), (96517, 1)] : List FactorBlock).map factorBlockValue).prod) = 1623791970233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_53
      · exact prime_oneHundredThirtyDX_39679
      · exact prime_oneHundredThirtyDX_96517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1623791970233) ^ 811895985116 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1623791970233) ^ 30637584344 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1623791970233) ^ 40923208 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1623791970233) ^ 16823896 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2008062150769 : Nat.Prime 2008062150769 := by
  apply lucas_primality 2008062150769 (14 : ZMod 2008062150769)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (13944876047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (13944876047, 1)] : List FactorBlock).map factorBlockValue).prod) = 2008062150769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_13944876047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 2008062150769) ^ 1004031075384 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (14 : ZMod 2008062150769) ^ 669354050256 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (14 : ZMod 2008062150769) ^ 144 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2376790715983 : Nat.Prime 2376790715983 := by
  apply lucas_primality 2376790715983 (3 : ZMod 2376790715983)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (396131785997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (396131785997, 1)] : List FactorBlock).map factorBlockValue).prod) = 2376790715983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_396131785997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2376790715983) ^ 1188395357991 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2376790715983) ^ 792263571994 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2376790715983) ^ 6 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2400049481591 : Nat.Prime 2400049481591 := by
  apply lucas_primality 2400049481591 (13 : ZMod 2400049481591)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (353, 1), (39994159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (353, 1), (39994159, 1)] : List FactorBlock).map factorBlockValue).prod) = 2400049481591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_353
      · exact prime_oneHundredThirtyDX_39994159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2400049481591) ^ 1200024740795 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 2400049481591) ^ 480009896318 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 2400049481591) ^ 141179381270 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 2400049481591) ^ 6799007030 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 2400049481591) ^ 60010 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2553097595771 : Nat.Prime 2553097595771 := by
  apply lucas_primality 2553097595771 (2 : ZMod 2553097595771)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (32717, 1), (269089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (32717, 1), (269089, 1)] : List FactorBlock).map factorBlockValue).prod) = 2553097595771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_29
      · exact prime_oneHundredThirtyDX_32717
      · exact prime_oneHundredThirtyDX_269089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2553097595771) ^ 1276548797885 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2553097595771) ^ 510619519154 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2553097595771) ^ 88037848130 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2553097595771) ^ 78035810 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2553097595771) ^ 9487930 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2676546708113 : Nat.Prime 2676546708113 := by
  apply lucas_primality 2676546708113 (3 : ZMod 2676546708113)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (107, 1), (28729, 1), (54419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (107, 1), (28729, 1), (54419, 1)] : List FactorBlock).map factorBlockValue).prod) = 2676546708113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_107
      · exact prime_oneHundredThirtyDX_28729
      · exact prime_oneHundredThirtyDX_54419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2676546708113) ^ 1338273354056 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 25014455216 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 93165328 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 49184048 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2848908483871 : Nat.Prime 2848908483871 := by
  apply lucas_primality 2848908483871 (13 : ZMod 2848908483871)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (157, 1), (8747, 1), (69151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (157, 1), (8747, 1), (69151, 1)] : List FactorBlock).map factorBlockValue).prod) = 2848908483871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_157
      · exact prime_oneHundredThirtyDX_8747
      · exact prime_oneHundredThirtyDX_69151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2848908483871) ^ 1424454241935 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 2848908483871) ^ 949636161290 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 2848908483871) ^ 569781696774 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 2848908483871) ^ 18145913910 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 2848908483871) ^ 325701210 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 2848908483871) ^ 41198370 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2852304439213 : Nat.Prime 2852304439213 := by
  apply lucas_primality 2852304439213 (2 : ZMod 2852304439213)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (101, 1), (2579, 1), (33797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (101, 1), (2579, 1), (33797, 1)] : List FactorBlock).map factorBlockValue).prod) = 2852304439213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_101
      · exact prime_oneHundredThirtyDX_2579
      · exact prime_oneHundredThirtyDX_33797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2852304439213) ^ 1426152219606 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2852304439213) ^ 950768146404 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2852304439213) ^ 28240638012 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2852304439213) ^ 1105973028 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2852304439213) ^ 84395196 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_3962303886571 : Nat.Prime 3962303886571 := by
  apply lucas_primality 3962303886571 (2 : ZMod 3962303886571)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (53, 1), (433, 1), (338543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (53, 1), (433, 1), (338543, 1)] : List FactorBlock).map factorBlockValue).prod) = 3962303886571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_53
      · exact prime_oneHundredThirtyDX_433
      · exact prime_oneHundredThirtyDX_338543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3962303886571) ^ 1981151943285 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3962303886571) ^ 1320767962190 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3962303886571) ^ 792460777314 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3962303886571) ^ 233076699210 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3962303886571) ^ 74760450690 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3962303886571) ^ 9150817290 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3962303886571) ^ 11703990 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_5267697195811 : Nat.Prime 5267697195811 := by
  apply lucas_primality 5267697195811 (2 : ZMod 5267697195811)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (29, 2), (41, 1), (42793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (29, 2), (41, 1), (42793, 1)] : List FactorBlock).map factorBlockValue).prod) = 5267697195811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_29
      · exact prime_oneHundredThirtyDX_41
      · exact prime_oneHundredThirtyDX_42793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5267697195811) ^ 2633848597905 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5267697195811) ^ 1755899065270 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5267697195811) ^ 1053539439162 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5267697195811) ^ 752528170830 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5267697195811) ^ 309864540930 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5267697195811) ^ 181644730890 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5267697195811) ^ 128480419410 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5267697195811) ^ 123097170 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_6477856359883 : Nat.Prime 6477856359883 := by
  apply lucas_primality 6477856359883 (2 : ZMod 6477856359883)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (10321, 1), (1035707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (10321, 1), (1035707, 1)] : List FactorBlock).map factorBlockValue).prod) = 6477856359883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_101
      · exact prime_oneHundredThirtyDX_10321
      · exact prime_oneHundredThirtyDX_1035707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6477856359883) ^ 3238928179941 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6477856359883) ^ 2159285453294 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6477856359883) ^ 64137191682 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6477856359883) ^ 627638442 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6477856359883) ^ 6254526 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_6789794634731 : Nat.Prime 6789794634731 := by
  apply lucas_primality 6789794634731 (2 : ZMod 6789794634731)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2473, 1), (12451, 1), (22051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2473, 1), (12451, 1), (22051, 1)] : List FactorBlock).map factorBlockValue).prod) = 6789794634731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_2473
      · exact prime_oneHundredThirtyDX_12451
      · exact prime_oneHundredThirtyDX_22051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6789794634731) ^ 3394897317365 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6789794634731) ^ 1357958926946 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6789794634731) ^ 2745570010 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6789794634731) ^ 545321230 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6789794634731) ^ 307913230 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_6809345431249 : Nat.Prime 6809345431249 := by
  apply lucas_primality 6809345431249 (29 : ZMod 6809345431249)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (141861363151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (141861363151, 1)] : List FactorBlock).map factorBlockValue).prod) = 6809345431249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_141861363151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (29 : ZMod 6809345431249) ^ 3404672715624 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (29 : ZMod 6809345431249) ^ 2269781810416 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (29 : ZMod 6809345431249) ^ 48 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_8524454832463 : Nat.Prime 8524454832463 := by
  apply lucas_primality 8524454832463 (3 : ZMod 8524454832463)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (74775919583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (74775919583, 1)] : List FactorBlock).map factorBlockValue).prod) = 8524454832463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_74775919583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8524454832463) ^ 4262227416231 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 2841484944154 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 448655517498 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 114 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_10640697366779 : Nat.Prime 10640697366779 := by
  apply lucas_primality 10640697366779 (2 : ZMod 10640697366779)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (503, 1), (4691, 1), (2254793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (503, 1), (4691, 1), (2254793, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640697366779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_503
      · exact prime_oneHundredThirtyDX_4691
      · exact prime_oneHundredThirtyDX_2254793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10640697366779) ^ 5320348683389 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 10640697366779) ^ 21154467926 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 10640697366779) ^ 2268321758 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 10640697366779) ^ 4719146 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_14966967343171 : Nat.Prime 14966967343171 := by
  apply lucas_primality 14966967343171 (2 : ZMod 14966967343171)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (498898911439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (498898911439, 1)] : List FactorBlock).map factorBlockValue).prod) = 14966967343171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_498898911439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14966967343171) ^ 7483483671585 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 14966967343171) ^ 4988989114390 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 14966967343171) ^ 2993393468634 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 14966967343171) ^ 30 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_17992248808559 : Nat.Prime 17992248808559 := by
  apply lucas_primality 17992248808559 (7 : ZMod 17992248808559)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (2699, 1), (196066613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (2699, 1), (196066613, 1)] : List FactorBlock).map factorBlockValue).prod) = 17992248808559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_2699
      · exact prime_oneHundredThirtyDX_196066613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 17992248808559) ^ 8996124404279 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 17992248808559) ^ 1058367576974 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 17992248808559) ^ 6666264842 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 17992248808559) ^ 91766 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_18655180611029 : Nat.Prime 18655180611029 := by
  apply lucas_primality 18655180611029 (2 : ZMod 18655180611029)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (358753473289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (358753473289, 1)] : List FactorBlock).map factorBlockValue).prod) = 18655180611029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_358753473289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18655180611029) ^ 9327590305514 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18655180611029) ^ 1435013893156 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18655180611029) ^ 52 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_21281394733559 : Nat.Prime 21281394733559 := by
  apply lucas_primality 21281394733559 (7 : ZMod 21281394733559)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10640697366779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10640697366779, 1)] : List FactorBlock).map factorBlockValue).prod) = 21281394733559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_10640697366779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 21281394733559) ^ 10640697366779 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 21281394733559) ^ 2 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_22733087583263 : Nat.Prime 22733087583263 := by
  apply lucas_primality 22733087583263 (5 : ZMod 22733087583263)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1623791970233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1623791970233, 1)] : List FactorBlock).map factorBlockValue).prod) = 22733087583263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_1623791970233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 22733087583263) ^ 11366543791631 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 22733087583263) ^ 3247583940466 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 22733087583263) ^ 14 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_30139788084221 : Nat.Prime 30139788084221 := by
  apply lucas_primality 30139788084221 (2 : ZMod 30139788084221)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1506989404211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1506989404211, 1)] : List FactorBlock).map factorBlockValue).prod) = 30139788084221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_1506989404211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30139788084221) ^ 15069894042110 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 30139788084221) ^ 6027957616844 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 30139788084221) ^ 20 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_30800900101879 : Nat.Prime 30800900101879 := by
  apply lucas_primality 30800900101879 (3 : ZMod 30800900101879)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (53, 1), (21407, 1), (79379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (53, 1), (21407, 1), (79379, 1)] : List FactorBlock).map factorBlockValue).prod) = 30800900101879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_53
      · exact prime_oneHundredThirtyDX_21407
      · exact prime_oneHundredThirtyDX_79379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30800900101879) ^ 15400450050939 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 30800900101879) ^ 10266966700626 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 30800900101879) ^ 1621100005362 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 30800900101879) ^ 581149058526 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 30800900101879) ^ 1438823754 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 30800900101879) ^ 388023282 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_33312673606897 : Nat.Prime 33312673606897 := by
  apply lucas_primality 33312673606897 (7 : ZMod 33312673606897)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (31, 1), (151, 2), (327289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (31, 1), (151, 2), (327289, 1)] : List FactorBlock).map factorBlockValue).prod) = 33312673606897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_31
      · exact prime_oneHundredThirtyDX_151
      · exact prime_oneHundredThirtyDX_327289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 33312673606897) ^ 16656336803448 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 11104224535632 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 1074602374416 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 220613732496 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 101783664 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_39131903192587 : Nat.Prime 39131903192587 := by
  apply lucas_primality 39131903192587 (2 : ZMod 39131903192587)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (54583, 1), (119487457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (54583, 1), (119487457, 1)] : List FactorBlock).map factorBlockValue).prod) = 39131903192587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_54583
      · exact prime_oneHundredThirtyDX_119487457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39131903192587) ^ 19565951596293 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 39131903192587) ^ 13043967730862 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 39131903192587) ^ 716924742 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 39131903192587) ^ 327498 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_49169667142223 : Nat.Prime 49169667142223 := by
  apply lucas_primality 49169667142223 (5 : ZMod 49169667142223)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23971, 1), (93237031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23971, 1), (93237031, 1)] : List FactorBlock).map factorBlockValue).prod) = 49169667142223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_23971
      · exact prime_oneHundredThirtyDX_93237031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 49169667142223) ^ 24584833571111 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 49169667142223) ^ 4469969740202 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 49169667142223) ^ 2051214682 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 49169667142223) ^ 527362 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_54348620161651 : Nat.Prime 54348620161651 := by
  apply lucas_primality 54348620161651 (19 : ZMod 54348620161651)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (73, 1), (83, 1), (139, 1), (281, 1), (1531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (73, 1), (83, 1), (139, 1), (281, 1), (1531, 1)] : List FactorBlock).map factorBlockValue).prod) = 54348620161651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_73
      · exact prime_oneHundredThirtyDX_83
      · exact prime_oneHundredThirtyDX_139
      · exact prime_oneHundredThirtyDX_281
      · exact prime_oneHundredThirtyDX_1531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 54348620161651) ^ 27174310080825 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (19 : ZMod 54348620161651) ^ 18116206720550 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (19 : ZMod 54348620161651) ^ 10869724032330 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (19 : ZMod 54348620161651) ^ 744501646050 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (19 : ZMod 54348620161651) ^ 654802652550 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (19 : ZMod 54348620161651) ^ 390997267350 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (19 : ZMod 54348620161651) ^ 193411459650 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (19 : ZMod 54348620161651) ^ 35498772150 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_57793874370247 : Nat.Prime 57793874370247 := by
  apply lucas_primality 57793874370247 (5 : ZMod 57793874370247)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17, 1), (96697, 1), (279029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17, 1), (96697, 1), (279029, 1)] : List FactorBlock).map factorBlockValue).prod) = 57793874370247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_96697
      · exact prime_oneHundredThirtyDX_279029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 57793874370247) ^ 28896937185123 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 19264624790082 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 8256267767178 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 3399639668838 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 597680118 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 207124974 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_61462197350923 : Nat.Prime 61462197350923 := by
  apply lucas_primality 61462197350923 (13 : ZMod 61462197350923)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1171, 1), (8747821997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1171, 1), (8747821997, 1)] : List FactorBlock).map factorBlockValue).prod) = 61462197350923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_1171
      · exact prime_oneHundredThirtyDX_8747821997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 61462197350923) ^ 30731098675461 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 61462197350923) ^ 20487399116974 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 61462197350923) ^ 52486931982 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 61462197350923) ^ 7026 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_64047370672577 : Nat.Prime 64047370672577 := by
  apply lucas_primality 64047370672577 (3 : ZMod 64047370672577)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (23, 1), (43510442033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (23, 1), (43510442033, 1)] : List FactorBlock).map factorBlockValue).prod) = 64047370672577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_23
      · exact prime_oneHundredThirtyDX_43510442033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 64047370672577) ^ 32023685336288 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 64047370672577) ^ 2784668290112 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 64047370672577) ^ 1472 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_70487035972141 : Nat.Prime 70487035972141 := by
  apply lucas_primality 70487035972141 (2 : ZMod 70487035972141)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (31, 1), (47, 1), (806303317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (31, 1), (47, 1), (806303317, 1)] : List FactorBlock).map factorBlockValue).prod) = 70487035972141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_31
      · exact prime_oneHundredThirtyDX_47
      · exact prime_oneHundredThirtyDX_806303317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70487035972141) ^ 35243517986070 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 70487035972141) ^ 23495678657380 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 70487035972141) ^ 14097407194428 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 70487035972141) ^ 2273775353940 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 70487035972141) ^ 1499724169620 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 70487035972141) ^ 87420 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_72493105517081 : Nat.Prime 72493105517081 := by
  apply lucas_primality 72493105517081 (3 : ZMod 72493105517081)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (73, 1), (24826405999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (73, 1), (24826405999, 1)] : List FactorBlock).map factorBlockValue).prod) = 72493105517081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_73
      · exact prime_oneHundredThirtyDX_24826405999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 72493105517081) ^ 36246552758540 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 72493105517081) ^ 14498621103416 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 72493105517081) ^ 993056239960 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 72493105517081) ^ 2920 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_90430304443429 : Nat.Prime 90430304443429 := by
  apply lucas_primality 90430304443429 (2 : ZMod 90430304443429)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1453, 1), (24181, 1), (214483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1453, 1), (24181, 1), (214483, 1)] : List FactorBlock).map factorBlockValue).prod) = 90430304443429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_1453
      · exact prime_oneHundredThirtyDX_24181
      · exact prime_oneHundredThirtyDX_214483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 90430304443429) ^ 45215152221714 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 90430304443429) ^ 30143434814476 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 90430304443429) ^ 62236961076 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 90430304443429) ^ 3739725588 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 90430304443429) ^ 421619916 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_100257985466497 : Nat.Prime 100257985466497 := by
  apply lucas_primality 100257985466497 (5 : ZMod 100257985466497)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) = 100257985466497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_173
      · exact prime_oneHundredThirtyDX_185153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 100257985466497) ^ 50128992733248 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 33419328488832 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 9114362315136 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 7712152728192 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 5276736077184 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 579525927552 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 541487232 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_102328915306291 : Nat.Prime 102328915306291 := by
  apply lucas_primality 102328915306291 (2 : ZMod 102328915306291)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (101, 1), (1907, 1), (17709449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (101, 1), (1907, 1), (17709449, 1)] : List FactorBlock).map factorBlockValue).prod) = 102328915306291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_101
      · exact prime_oneHundredThirtyDX_1907
      · exact prime_oneHundredThirtyDX_17709449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 102328915306291) ^ 51164457653145 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 102328915306291) ^ 34109638435430 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 102328915306291) ^ 20465783061258 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 102328915306291) ^ 1013157577290 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 102328915306291) ^ 53659630470 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 102328915306291) ^ 5778210 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_115342509540833 : Nat.Prime 115342509540833 := by
  apply lucas_primality 115342509540833 (3 : ZMod 115342509540833)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (2777, 1), (185423809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (2777, 1), (185423809, 1)] : List FactorBlock).map factorBlockValue).prod) = 115342509540833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_2777
      · exact prime_oneHundredThirtyDX_185423809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 115342509540833) ^ 57671254770416 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 16477501362976 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 41534933216 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 622048 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_216517044774197 : Nat.Prime 216517044774197 := by
  apply lucas_primality 216517044774197 (2 : ZMod 216517044774197)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (2848908483871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (2848908483871, 1)] : List FactorBlock).map factorBlockValue).prod) = 216517044774197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_2848908483871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 216517044774197) ^ 108258522387098 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 216517044774197) ^ 11395633935484 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 216517044774197) ^ 76 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_267494201311979 : Nat.Prime 267494201311979 := by
  apply lucas_primality 267494201311979 (6 : ZMod 267494201311979)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (107, 1), (12886318591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (107, 1), (12886318591, 1)] : List FactorBlock).map factorBlockValue).prod) = 267494201311979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_97
      · exact prime_oneHundredThirtyDX_107
      · exact prime_oneHundredThirtyDX_12886318591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 267494201311979) ^ 133747100655989 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 2757672178474 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 2499945806654 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 20758 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_281782374136027 : Nat.Prime 281782374136027 := by
  apply lucas_primality 281782374136027 (2 : ZMod 281782374136027)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (1145456805431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (1145456805431, 1)] : List FactorBlock).map factorBlockValue).prod) = 281782374136027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_41
      · exact prime_oneHundredThirtyDX_1145456805431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 281782374136027) ^ 140891187068013 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 281782374136027) ^ 93927458045342 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 281782374136027) ^ 6872740832586 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 281782374136027) ^ 246 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_295250682167513 : Nat.Prime 295250682167513 := by
  apply lucas_primality 295250682167513 (3 : ZMod 295250682167513)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (137, 1), (2593, 1), (103890979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (137, 1), (2593, 1), (103890979, 1)] : List FactorBlock).map factorBlockValue).prod) = 295250682167513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_137
      · exact prime_oneHundredThirtyDX_2593
      · exact prime_oneHundredThirtyDX_103890979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 295250682167513) ^ 147625341083756 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 295250682167513) ^ 2155114468376 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 295250682167513) ^ 113864512984 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 295250682167513) ^ 2841928 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_633968621851361 : Nat.Prime 633968621851361 := by
  apply lucas_primality 633968621851361 (3 : ZMod 633968621851361)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (3962303886571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (3962303886571, 1)] : List FactorBlock).map factorBlockValue).prod) = 633968621851361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_3962303886571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 633968621851361) ^ 316984310925680 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 633968621851361) ^ 126793724370272 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 633968621851361) ^ 160 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_810117218002061 : Nat.Prime 810117218002061 := by
  apply lucas_primality 810117218002061 (2 : ZMod 810117218002061)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (79, 1), (22292713759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (79, 1), (22292713759, 1)] : List FactorBlock).map factorBlockValue).prod) = 810117218002061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_23
      · exact prime_oneHundredThirtyDX_79
      · exact prime_oneHundredThirtyDX_22292713759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 810117218002061) ^ 405058609001030 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 810117218002061) ^ 162023443600412 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 810117218002061) ^ 35222487739220 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 810117218002061) ^ 10254648329140 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 810117218002061) ^ 36340 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1038420129311893 : Nat.Prime 1038420129311893 := by
  apply lucas_primality 1038420129311893 (2 : ZMod 1038420129311893)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (83, 1), (5711, 1), (60852769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (83, 1), (5711, 1), (60852769, 1)] : List FactorBlock).map factorBlockValue).prod) = 1038420129311893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_83
      · exact prime_oneHundredThirtyDX_5711
      · exact prime_oneHundredThirtyDX_60852769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1038420129311893) ^ 519210064655946 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1038420129311893) ^ 346140043103964 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1038420129311893) ^ 12511085895324 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1038420129311893) ^ 181828073772 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1038420129311893) ^ 17064468 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1090601907139847 : Nat.Prime 1090601907139847 := by
  apply lucas_primality 1090601907139847 (5 : ZMod 1090601907139847)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (2679647, 1), (4963349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (2679647, 1), (4963349, 1)] : List FactorBlock).map factorBlockValue).prod) = 1090601907139847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_41
      · exact prime_oneHundredThirtyDX_2679647
      · exact prime_oneHundredThirtyDX_4963349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1090601907139847) ^ 545300953569923 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1090601907139847) ^ 26600046515606 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1090601907139847) ^ 406994618 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1090601907139847) ^ 219731054 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1173957095777611 : Nat.Prime 1173957095777611 := by
  apply lucas_primality 1173957095777611 (10 : ZMod 1173957095777611)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (39131903192587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (39131903192587, 1)] : List FactorBlock).map factorBlockValue).prod) = 1173957095777611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_39131903192587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1173957095777611) ^ 586978547888805 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (10 : ZMod 1173957095777611) ^ 391319031925870 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (10 : ZMod 1173957095777611) ^ 234791419155522 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (10 : ZMod 1173957095777611) ^ 30 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2159069857027081 : Nat.Prime 2159069857027081 := by
  apply lucas_primality 2159069857027081 (7 : ZMod 2159069857027081)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17992248808559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17992248808559, 1)] : List FactorBlock).map factorBlockValue).prod) = 2159069857027081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_17992248808559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2159069857027081) ^ 1079534928513540 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2159069857027081) ^ 719689952342360 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2159069857027081) ^ 431813971405416 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2159069857027081) ^ 120 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2327374908725599 : Nat.Prime 2327374908725599 := by
  apply lucas_primality 2327374908725599 (3 : ZMod 2327374908725599)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (80071, 1), (1614799441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (80071, 1), (1614799441, 1)] : List FactorBlock).map factorBlockValue).prod) = 2327374908725599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_80071
      · exact prime_oneHundredThirtyDX_1614799441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2327374908725599) ^ 1163687454362799 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2327374908725599) ^ 775791636241866 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2327374908725599) ^ 29066389938 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2327374908725599) ^ 1441278 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2458487894036921 : Nat.Prime 2458487894036921 := by
  apply lucas_primality 2458487894036921 (3 : ZMod 2458487894036921)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (61462197350923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (61462197350923, 1)] : List FactorBlock).map factorBlockValue).prod) = 2458487894036921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_61462197350923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2458487894036921) ^ 1229243947018460 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2458487894036921) ^ 491697578807384 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2458487894036921) ^ 40 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_3258568895629807 : Nat.Prime 3258568895629807 := by
  apply lucas_primality 3258568895629807 (3 : ZMod 3258568895629807)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 2), (1789, 1), (278764481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 2), (1789, 1), (278764481, 1)] : List FactorBlock).map factorBlockValue).prod) = 3258568895629807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_1789
      · exact prime_oneHundredThirtyDX_278764481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3258568895629807) ^ 1629284447814903 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3258568895629807) ^ 1086189631876602 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3258568895629807) ^ 296233535966346 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3258568895629807) ^ 1821447118854 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3258568895629807) ^ 11689326 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_6693899198418583 : Nat.Prime 6693899198418583 := by
  apply lucas_primality 6693899198418583 (3 : ZMod 6693899198418583)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (4327, 1), (14639, 1), (212203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (4327, 1), (14639, 1), (212203, 1)] : List FactorBlock).map factorBlockValue).prod) = 6693899198418583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_83
      · exact prime_oneHundredThirtyDX_4327
      · exact prime_oneHundredThirtyDX_14639
      · exact prime_oneHundredThirtyDX_212203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6693899198418583) ^ 3346949599209291 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6693899198418583) ^ 2231299732806194 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6693899198418583) ^ 80649387932754 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6693899198418583) ^ 1547006979066 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6693899198418583) ^ 457264785738 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6693899198418583) ^ 31544790594 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_8025537258252043 : Nat.Prime 8025537258252043 := by
  apply lucas_primality 8025537258252043 (2 : ZMod 8025537258252043)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (197, 1), (6789794634731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (197, 1), (6789794634731, 1)] : List FactorBlock).map factorBlockValue).prod) = 8025537258252043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_197
      · exact prime_oneHundredThirtyDX_6789794634731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8025537258252043) ^ 4012768629126021 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8025537258252043) ^ 2675179086084014 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8025537258252043) ^ 40738767808386 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8025537258252043) ^ 1182 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_8151940739207033 : Nat.Prime 8151940739207033 := by
  apply lucas_primality 8151940739207033 (3 : ZMod 8151940739207033)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (997, 1), (1022058768707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (997, 1), (1022058768707, 1)] : List FactorBlock).map factorBlockValue).prod) = 8151940739207033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_997
      · exact prime_oneHundredThirtyDX_1022058768707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8151940739207033) ^ 4075970369603516 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 8151940739207033) ^ 8176470149656 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 8151940739207033) ^ 7976 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_8560070626452379 : Nat.Prime 8560070626452379 := by
  apply lucas_primality 8560070626452379 (2 : ZMod 8560070626452379)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1093, 1), (118662433481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1093, 1), (118662433481, 1)] : List FactorBlock).map factorBlockValue).prod) = 8560070626452379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_1093
      · exact prime_oneHundredThirtyDX_118662433481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8560070626452379) ^ 4280035313226189 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 2853356875484126 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 778188238768398 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 7831720609746 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 72138 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_15101611334912527 : Nat.Prime 15101611334912527 := by
  apply lucas_primality 15101611334912527 (5 : ZMod 15101611334912527)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3331, 1), (395611, 1), (1909981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3331, 1), (395611, 1), (1909981, 1)] : List FactorBlock).map factorBlockValue).prod) = 15101611334912527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_3331
      · exact prime_oneHundredThirtyDX_395611
      · exact prime_oneHundredThirtyDX_1909981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 15101611334912527) ^ 7550805667456263 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 15101611334912527) ^ 5033870444970842 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 15101611334912527) ^ 4533656960346 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 15101611334912527) ^ 38172880266 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 15101611334912527) ^ 7906681446 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_17628347298882679 : Nat.Prime 17628347298882679 := by
  apply lucas_primality 17628347298882679 (3 : ZMod 17628347298882679)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (44543, 1), (65960035991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (44543, 1), (65960035991, 1)] : List FactorBlock).map factorBlockValue).prod) = 17628347298882679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_44543
      · exact prime_oneHundredThirtyDX_65960035991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 17628347298882679) ^ 8814173649441339 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 17628347298882679) ^ 5876115766294226 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 17628347298882679) ^ 395760215946 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 17628347298882679) ^ 267258 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_32384069730307111 : Nat.Prime 32384069730307111 := by
  apply lucas_primality 32384069730307111 (3 : ZMod 32384069730307111)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (20297, 1), (53183672021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (20297, 1), (53183672021, 1)] : List FactorBlock).map factorBlockValue).prod) = 32384069730307111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_20297
      · exact prime_oneHundredThirtyDX_53183672021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32384069730307111) ^ 16192034865153555 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 32384069730307111) ^ 10794689910102370 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 32384069730307111) ^ 6476813946061422 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 32384069730307111) ^ 1595510160630 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 32384069730307111) ^ 608910 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_33529869781467167 : Nat.Prime 33529869781467167 := by
  apply lucas_primality 33529869781467167 (5 : ZMod 33529869781467167)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2011, 1), (4721, 1), (1765858093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2011, 1), (4721, 1), (1765858093, 1)] : List FactorBlock).map factorBlockValue).prod) = 33529869781467167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_2011
      · exact prime_oneHundredThirtyDX_4721
      · exact prime_oneHundredThirtyDX_1765858093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33529869781467167) ^ 16764934890733583 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 33529869781467167) ^ 16673232114106 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 33529869781467167) ^ 7102281250046 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 33529869781467167) ^ 18987862 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_38265826765415749 : Nat.Prime 38265826765415749 := by
  apply lucas_primality 38265826765415749 (2 : ZMod 38265826765415749)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1249, 1), (2553097595771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1249, 1), (2553097595771, 1)] : List FactorBlock).map factorBlockValue).prod) = 38265826765415749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_1249
      · exact prime_oneHundredThirtyDX_2553097595771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 38265826765415749) ^ 19132913382707874 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 38265826765415749) ^ 12755275588471916 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 38265826765415749) ^ 30637171149252 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 38265826765415749) ^ 14988 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_39759549843214027 : Nat.Prime 39759549843214027 := by
  apply lucas_primality 39759549843214027 (2 : ZMod 39759549843214027)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (31, 1), (283, 1), (4001, 1), (2996629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (31, 1), (283, 1), (4001, 1), (2996629, 1)] : List FactorBlock).map factorBlockValue).prod) = 39759549843214027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_31
      · exact prime_oneHundredThirtyDX_283
      · exact prime_oneHundredThirtyDX_4001
      · exact prime_oneHundredThirtyDX_2996629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39759549843214027) ^ 19879774921607013 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 39759549843214027) ^ 13253183281071342 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 39759549843214027) ^ 5679935691887718 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 39759549843214027) ^ 1282566123974646 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 39759549843214027) ^ 140493108986622 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 39759549843214027) ^ 9937403110026 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 39759549843214027) ^ 13268092194 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_42262455447993997 : Nat.Prime 42262455447993997 := by
  apply lucas_primality 42262455447993997 (2 : ZMod 42262455447993997)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1173957095777611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1173957095777611, 1)] : List FactorBlock).map factorBlockValue).prod) = 42262455447993997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_1173957095777611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 42262455447993997) ^ 21131227723996998 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 42262455447993997) ^ 14087485149331332 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 42262455447993997) ^ 36 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_43246997146607257 : Nat.Prime 43246997146607257 := by
  apply lucas_primality 43246997146607257 (5 : ZMod 43246997146607257)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (199, 1), (1006118489359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (199, 1), (1006118489359, 1)] : List FactorBlock).map factorBlockValue).prod) = 43246997146607257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_199
      · exact prime_oneHundredThirtyDX_1006118489359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 43246997146607257) ^ 21623498573303628 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 43246997146607257) ^ 14415665715535752 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 43246997146607257) ^ 217321593701544 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 43246997146607257) ^ 42984 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_48153223549512259 : Nat.Prime 48153223549512259 := by
  apply lucas_primality 48153223549512259 (3 : ZMod 48153223549512259)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8025537258252043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8025537258252043, 1)] : List FactorBlock).map factorBlockValue).prod) = 48153223549512259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_8025537258252043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 48153223549512259) ^ 24076611774756129 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 48153223549512259) ^ 16051074516504086 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 48153223549512259) ^ 6 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_48749844113165203 : Nat.Prime 48749844113165203 := by
  apply lucas_primality 48749844113165203 (2 : ZMod 48749844113165203)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (19, 1), (43891, 1), (28405261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (19, 1), (43891, 1), (28405261, 1)] : List FactorBlock).map factorBlockValue).prod) = 48749844113165203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_43891
      · exact prime_oneHundredThirtyDX_28405261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 48749844113165203) ^ 24374922056582601 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 48749844113165203) ^ 16249948037721734 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 48749844113165203) ^ 6964263444737886 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 48749844113165203) ^ 2565781269113958 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 48749844113165203) ^ 1110702515622 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 48749844113165203) ^ 1716225882 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_50012231077210697 : Nat.Prime 50012231077210697 := by
  apply lucas_primality 50012231077210697 (3 : ZMod 50012231077210697)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (31, 1), (79, 1), (167, 1), (2909, 1), (750653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (31, 1), (79, 1), (167, 1), (2909, 1), (750653, 1)] : List FactorBlock).map factorBlockValue).prod) = 50012231077210697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_31
      · exact prime_oneHundredThirtyDX_79
      · exact prime_oneHundredThirtyDX_167
      · exact prime_oneHundredThirtyDX_2909
      · exact prime_oneHundredThirtyDX_750653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 50012231077210697) ^ 25006115538605348 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 50012231077210697) ^ 7144604439601528 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 50012231077210697) ^ 1613297776684216 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 50012231077210697) ^ 633066216167224 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 50012231077210697) ^ 299474437588088 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 50012231077210697) ^ 17192241690344 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 50012231077210697) ^ 66624966632 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_54505364198768423 : Nat.Prime 54505364198768423 := by
  apply lucas_primality 54505364198768423 (5 : ZMod 54505364198768423)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (139, 1), (8524454832463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (139, 1), (8524454832463, 1)] : List FactorBlock).map factorBlockValue).prod) = 54505364198768423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_23
      · exact prime_oneHundredThirtyDX_139
      · exact prime_oneHundredThirtyDX_8524454832463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 54505364198768423) ^ 27252682099384211 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 2369798443424714 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 392124922293298 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 6394 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_64664799428838823 : Nat.Prime 64664799428838823 := by
  apply lucas_primality 64664799428838823 (3 : ZMod 64664799428838823)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (633968621851361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (633968621851361, 1)] : List FactorBlock).map factorBlockValue).prod) = 64664799428838823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_633968621851361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 64664799428838823) ^ 32332399714419411 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 64664799428838823) ^ 21554933142946274 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 64664799428838823) ^ 3803811731108166 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 64664799428838823) ^ 102 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_83886273557254331 : Nat.Prime 83886273557254331 := by
  apply lucas_primality 83886273557254331 (6 : ZMod 83886273557254331)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (173, 1), (2852304439213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (173, 1), (2852304439213, 1)] : List FactorBlock).map factorBlockValue).prod) = 83886273557254331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_173
      · exact prime_oneHundredThirtyDX_2852304439213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 83886273557254331) ^ 41943136778627165 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 83886273557254331) ^ 16777254711450866 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 83886273557254331) ^ 4934486679838490 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 83886273557254331) ^ 484891754666210 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 83886273557254331) ^ 29410 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_88424436268679879 : Nat.Prime 88424436268679879 := by
  apply lucas_primality 88424436268679879 (7 : ZMod 88424436268679879)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2677099, 1), (16514973161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2677099, 1), (16514973161, 1)] : List FactorBlock).map factorBlockValue).prod) = 88424436268679879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_2677099
      · exact prime_oneHundredThirtyDX_16514973161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 88424436268679879) ^ 44212218134339939 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 88424436268679879) ^ 33029946322 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 88424436268679879) ^ 5354198 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_152210232520093753 : Nat.Prime 152210232520093753 := by
  apply lucas_primality 152210232520093753 (5 : ZMod 152210232520093753)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (25923907, 1), (244642639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (25923907, 1), (244642639, 1)] : List FactorBlock).map factorBlockValue).prod) = 152210232520093753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_25923907
      · exact prime_oneHundredThirtyDX_244642639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 152210232520093753) ^ 76105116260046876 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 152210232520093753) ^ 50736744173364584 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 152210232520093753) ^ 5871423336 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 152210232520093753) ^ 622173768 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_177112743868002511 : Nat.Prime 177112743868002511 := by
  apply lucas_primality 177112743868002511 (6 : ZMod 177112743868002511)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (281, 1), (678593, 1), (10320283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (281, 1), (678593, 1), (10320283, 1)] : List FactorBlock).map factorBlockValue).prod) = 177112743868002511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_281
      · exact prime_oneHundredThirtyDX_678593
      · exact prime_oneHundredThirtyDX_10320283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 177112743868002511) ^ 88556371934001255 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 59037581289334170 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 35422548773600502 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 630294462163710 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 260999957070 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 17161616970 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_178858712770934909 : Nat.Prime 178858712770934909 := by
  apply lucas_primality 178858712770934909 (2 : ZMod 178858712770934909)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (1090601907139847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (1090601907139847, 1)] : List FactorBlock).map factorBlockValue).prod) = 178858712770934909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_41
      · exact prime_oneHundredThirtyDX_1090601907139847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 178858712770934909) ^ 89429356385467454 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 178858712770934909) ^ 4362407628559388 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 178858712770934909) ^ 164 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_246305842413683527 : Nat.Prime 246305842413683527 := by
  apply lucas_primality 246305842413683527 (3 : ZMod 246305842413683527)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (661, 1), (8839, 1), (2342057833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (661, 1), (8839, 1), (2342057833, 1)] : List FactorBlock).map factorBlockValue).prod) = 246305842413683527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_661
      · exact prime_oneHundredThirtyDX_8839
      · exact prime_oneHundredThirtyDX_2342057833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 246305842413683527) ^ 123152921206841763 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 246305842413683527) ^ 82101947471227842 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 246305842413683527) ^ 372626085345966 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 246305842413683527) ^ 27865804097034 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 246305842413683527) ^ 105166422 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_288505200367772279 : Nat.Prime 288505200367772279 := by
  apply lucas_primality 288505200367772279 (13 : ZMod 288505200367772279)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (593, 1), (773, 1), (1243852667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (593, 1), (773, 1), (1243852667, 1)] : List FactorBlock).map factorBlockValue).prod) = 288505200367772279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_23
      · exact prime_oneHundredThirtyDX_593
      · exact prime_oneHundredThirtyDX_773
      · exact prime_oneHundredThirtyDX_1243852667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 288505200367772279) ^ 144252600183886139 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 288505200367772279) ^ 26227745487979298 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 288505200367772279) ^ 12543704363816186 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 288505200367772279) ^ 486518044465046 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 288505200367772279) ^ 373227943554686 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (13 : ZMod 288505200367772279) ^ 231944834 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_417636636125115401 : Nat.Prime 417636636125115401 := by
  apply lucas_primality 417636636125115401 (3 : ZMod 417636636125115401)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (7, 2), (17, 1), (1275749, 1), (1964981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (7, 2), (17, 1), (1275749, 1), (1964981, 1)] : List FactorBlock).map factorBlockValue).prod) = 417636636125115401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_1275749
      · exact prime_oneHundredThirtyDX_1964981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 417636636125115401) ^ 208818318062557700 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 417636636125115401) ^ 83527327225023080 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 417636636125115401) ^ 59662376589302200 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 417636636125115401) ^ 24566860948536200 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 417636636125115401) ^ 327365834600 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 417636636125115401) ^ 212539783400 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_467644591344983909 : Nat.Prime 467644591344983909 := by
  apply lucas_primality 467644591344983909 (2 : ZMod 467644591344983909)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4733, 1), (7919, 1), (3119242051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4733, 1), (7919, 1), (3119242051, 1)] : List FactorBlock).map factorBlockValue).prod) = 467644591344983909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_4733
      · exact prime_oneHundredThirtyDX_7919
      · exact prime_oneHundredThirtyDX_3119242051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 467644591344983909) ^ 233822295672491954 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 467644591344983909) ^ 98805111207476 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 467644591344983909) ^ 59053490509532 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 467644591344983909) ^ 149922508 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_525646413082499593 : Nat.Prime 525646413082499593 := by
  apply lucas_primality 525646413082499593 (5 : ZMod 525646413082499593)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (839, 1), (2008062150769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (839, 1), (2008062150769, 1)] : List FactorBlock).map factorBlockValue).prod) = 525646413082499593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_839
      · exact prime_oneHundredThirtyDX_2008062150769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 525646413082499593) ^ 262823206541249796 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 525646413082499593) ^ 175215471027499864 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 525646413082499593) ^ 40434339467884584 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 525646413082499593) ^ 626515391039928 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 525646413082499593) ^ 261768 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_814468421742501887 : Nat.Prime 814468421742501887 := by
  apply lucas_primality 814468421742501887 (5 : ZMod 814468421742501887)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (127, 1), (54348620161651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (127, 1), (54348620161651, 1)] : List FactorBlock).map factorBlockValue).prod) = 814468421742501887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_59
      · exact prime_oneHundredThirtyDX_127
      · exact prime_oneHundredThirtyDX_54348620161651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 814468421742501887) ^ 407234210871250943 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 814468421742501887) ^ 13804549521059354 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 814468421742501887) ^ 6413137179074818 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 814468421742501887) ^ 14986 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_947523074430697211 : Nat.Prime 947523074430697211 := by
  apply lucas_primality 947523074430697211 (2 : ZMod 947523074430697211)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (2389, 1), (1367652133241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (2389, 1), (1367652133241, 1)] : List FactorBlock).map factorBlockValue).prod) = 947523074430697211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_29
      · exact prime_oneHundredThirtyDX_2389
      · exact prime_oneHundredThirtyDX_1367652133241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 947523074430697211) ^ 473761537215348605 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 947523074430697211) ^ 189504614886139442 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 947523074430697211) ^ 32673209463127490 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 947523074430697211) ^ 396619118639890 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 947523074430697211) ^ 692810 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1319589698123917111 : Nat.Prime 1319589698123917111 := by
  apply lucas_primality 1319589698123917111 (3 : ZMod 1319589698123917111)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (36097, 1), (110778088511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (36097, 1), (110778088511, 1)] : List FactorBlock).map factorBlockValue).prod) = 1319589698123917111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_36097
      · exact prime_oneHundredThirtyDX_110778088511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1319589698123917111) ^ 659794849061958555 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1319589698123917111) ^ 439863232707972370 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1319589698123917111) ^ 263917939624783422 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1319589698123917111) ^ 119962699829447010 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1319589698123917111) ^ 36556769208630 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1319589698123917111) ^ 11912010 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1473596414167950607 : Nat.Prime 1473596414167950607 := by
  apply lucas_primality 1473596414167950607 (3 : ZMod 1473596414167950607)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (173, 1), (883, 1), (14750067271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (173, 1), (883, 1), (14750067271, 1)] : List FactorBlock).map factorBlockValue).prod) = 1473596414167950607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_109
      · exact prime_oneHundredThirtyDX_173
      · exact prime_oneHundredThirtyDX_883
      · exact prime_oneHundredThirtyDX_14750067271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1473596414167950607) ^ 736798207083975303 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1473596414167950607) ^ 491198804722650202 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1473596414167950607) ^ 13519233157504134 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1473596414167950607) ^ 8517898347791622 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1473596414167950607) ^ 1668852111175482 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1473596414167950607) ^ 99904386 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1895046148861394423 : Nat.Prime 1895046148861394423 := by
  apply lucas_primality 1895046148861394423 (5 : ZMod 1895046148861394423)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (947523074430697211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (947523074430697211, 1)] : List FactorBlock).map factorBlockValue).prod) = 1895046148861394423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_947523074430697211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1895046148861394423) ^ 947523074430697211 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1895046148861394423) ^ 2 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2053819141548103673 : Nat.Prime 2053819141548103673 := by
  apply lucas_primality 2053819141548103673 (3 : ZMod 2053819141548103673)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (15101611334912527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (15101611334912527, 1)] : List FactorBlock).map factorBlockValue).prod) = 2053819141548103673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_15101611334912527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2053819141548103673) ^ 1026909570774051836 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2053819141548103673) ^ 120812890679300216 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2053819141548103673) ^ 136 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_101
      · exact prime_oneHundredThirtyDX_191
      · exact prime_oneHundredThirtyDX_48017
      · exact prime_oneHundredThirtyDX_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2927544154246713619 : Nat.Prime 2927544154246713619 := by
  apply lucas_primality 2927544154246713619 (3 : ZMod 2927544154246713619)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (8560070626452379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (8560070626452379, 1)] : List FactorBlock).map factorBlockValue).prod) = 2927544154246713619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_8560070626452379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2927544154246713619) ^ 1463772077123356809 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 975848051415571206 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 154081271276142822 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 342 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_3014995691311940443 : Nat.Prime 3014995691311940443 := by
  apply lucas_primality 3014995691311940443 (2 : ZMod 3014995691311940443)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (321187, 1), (1564506913061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (321187, 1), (1564506913061, 1)] : List FactorBlock).map factorBlockValue).prod) = 3014995691311940443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_321187
      · exact prime_oneHundredThirtyDX_1564506913061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3014995691311940443) ^ 1507497845655970221 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 1004998563770646814 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 9387041478366 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 1927122 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_3459253030453840597 : Nat.Prime 3459253030453840597 := by
  apply lucas_primality 3459253030453840597 (5 : ZMod 3459253030453840597)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (44501, 1), (6477856359883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (44501, 1), (6477856359883, 1)] : List FactorBlock).map factorBlockValue).prod) = 3459253030453840597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_44501
      · exact prime_oneHundredThirtyDX_6477856359883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3459253030453840597) ^ 1729626515226920298 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 3459253030453840597) ^ 1153084343484613532 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 3459253030453840597) ^ 77734276318596 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 3459253030453840597) ^ 534012 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_4292609106502437817 : Nat.Prime 4292609106502437817 := by
  apply lucas_primality 4292609106502437817 (7 : ZMod 4292609106502437817)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (178858712770934909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (178858712770934909, 1)] : List FactorBlock).map factorBlockValue).prod) = 4292609106502437817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_178858712770934909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4292609106502437817) ^ 2146304553251218908 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 4292609106502437817) ^ 1430869702167479272 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 4292609106502437817) ^ 24 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_4915900423864514951 : Nat.Prime 4915900423864514951 := by
  apply lucas_primality 4915900423864514951 (22 : ZMod 4915900423864514951)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (6569, 1), (14966967343171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (6569, 1), (14966967343171, 1)] : List FactorBlock).map factorBlockValue).prod) = 4915900423864514951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_6569
      · exact prime_oneHundredThirtyDX_14966967343171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (22 : ZMod 4915900423864514951) ^ 2457950211932257475 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (22 : ZMod 4915900423864514951) ^ 983180084772902990 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (22 : ZMod 4915900423864514951) ^ 748348367158550 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (22 : ZMod 4915900423864514951) ^ 328450 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_9310276483619584019 : Nat.Prime 9310276483619584019 := by
  apply lucas_primality 9310276483619584019 (2 : ZMod 9310276483619584019)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 2), (101, 1), (37573, 1), (1036932751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 2), (101, 1), (37573, 1), (1036932751, 1)] : List FactorBlock).map factorBlockValue).prod) = 9310276483619584019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_101
      · exact prime_oneHundredThirtyDX_37573
      · exact prime_oneHundredThirtyDX_1036932751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9310276483619584019) ^ 4655138241809792009 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310276483619584019) ^ 1330039497659940574 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310276483619584019) ^ 716175114124583386 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310276483619584019) ^ 92180955283362218 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310276483619584019) ^ 247791671775466 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310276483619584019) ^ 8978669518 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_11501317095805079167 : Nat.Prime 11501317095805079167 := by
  apply lucas_primality 11501317095805079167 (5 : ZMod 11501317095805079167)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19, 1), (23, 1), (32779, 1), (33739, 1), (305101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19, 1), (23, 1), (32779, 1), (33739, 1), (305101, 1)] : List FactorBlock).map factorBlockValue).prod) = 11501317095805079167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_23
      · exact prime_oneHundredThirtyDX_32779
      · exact prime_oneHundredThirtyDX_33739
      · exact prime_oneHundredThirtyDX_305101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11501317095805079167) ^ 5750658547902539583 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11501317095805079167) ^ 3833772365268359722 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11501317095805079167) ^ 884716699677313782 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11501317095805079167) ^ 605332478726583114 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11501317095805079167) ^ 500057265035003442 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11501317095805079167) ^ 350874556752954 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11501317095805079167) ^ 340890870974394 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11501317095805079167) ^ 37696753192566 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_19020649354603392817 : Nat.Prime 19020649354603392817 := by
  apply lucas_primality 19020649354603392817 (5 : ZMod 19020649354603392817)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (17, 1), (14951, 1), (537157, 1), (967481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (17, 1), (14951, 1), (537157, 1), (967481, 1)] : List FactorBlock).map factorBlockValue).prod) = 19020649354603392817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_14951
      · exact prime_oneHundredThirtyDX_537157
      · exact prime_oneHundredThirtyDX_967481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 19020649354603392817) ^ 9510324677301696408 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 19020649354603392817) ^ 6340216451534464272 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 19020649354603392817) ^ 1118861726741376048 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 19020649354603392817) ^ 1272199140833616 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 19020649354603392817) ^ 35409851039088 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 19020649354603392817) ^ 19659971983536 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_35637185932538362091 : Nat.Prime 35637185932538362091 := by
  apply lucas_primality 35637185932538362091 (2 : ZMod 35637185932538362091)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (19, 1), (8494391, 1), (1298878813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (19, 1), (8494391, 1), (1298878813, 1)] : List FactorBlock).map factorBlockValue).prod) = 35637185932538362091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_8494391
      · exact prime_oneHundredThirtyDX_1298878813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35637185932538362091) ^ 17818592966269181045 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 35637185932538362091) ^ 7127437186507672418 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 35637185932538362091) ^ 2096305054855197770 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 35637185932538362091) ^ 1875641364870440110 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 35637185932538362091) ^ 4195378565990 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 35637185932538362091) ^ 27436882930 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_52983531609217552957 : Nat.Prime 52983531609217552957 := by
  apply lucas_primality 52983531609217552957 (5 : ZMod 52983531609217552957)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) = 52983531609217552957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_2063
      · exact prime_oneHundredThirtyDX_15269
      · exact prime_oneHundredThirtyDX_140168308879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52983531609217552957) ^ 26491765804608776478 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 17661177203072517652 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 25682758899281412 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 3470006654608524 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 377999364 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_57536587183308550771 : Nat.Prime 57536587183308550771 := by
  apply lucas_primality 57536587183308550771 (2 : ZMod 57536587183308550771)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2887, 1), (1026101, 1), (647419757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2887, 1), (1026101, 1), (647419757, 1)] : List FactorBlock).map factorBlockValue).prod) = 57536587183308550771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_2887
      · exact prime_oneHundredThirtyDX_1026101
      · exact prime_oneHundredThirtyDX_647419757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57536587183308550771) ^ 28768293591654275385 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 57536587183308550771) ^ 19178862394436183590 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 57536587183308550771) ^ 11507317436661710154 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 57536587183308550771) ^ 19929541802323710 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 57536587183308550771) ^ 56073025153770 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 57536587183308550771) ^ 88870607610 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_61530718043549270167 : Nat.Prime 61530718043549270167 := by
  apply lucas_primality 61530718043549270167 (3 : ZMod 61530718043549270167)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (229, 1), (379033, 1), (16878357739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (229, 1), (379033, 1), (16878357739, 1)] : List FactorBlock).map factorBlockValue).prod) = 61530718043549270167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_229
      · exact prime_oneHundredThirtyDX_379033
      · exact prime_oneHundredThirtyDX_16878357739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 61530718043549270167) ^ 30765359021774635083 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 61530718043549270167) ^ 20510239347849756722 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 61530718043549270167) ^ 8790102577649895738 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 61530718043549270167) ^ 268693091893228254 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 61530718043549270167) ^ 162336044733702 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 61530718043549270167) ^ 3645539394 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_105131039647847779157 : Nat.Prime 105131039647847779157 := by
  apply lucas_primality 105131039647847779157 (2 : ZMod 105131039647847779157)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (173, 1), (1831, 1), (2676546708113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (173, 1), (1831, 1), (2676546708113, 1)] : List FactorBlock).map factorBlockValue).prod) = 105131039647847779157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_31
      · exact prime_oneHundredThirtyDX_173
      · exact prime_oneHundredThirtyDX_1831
      · exact prime_oneHundredThirtyDX_2676546708113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 105131039647847779157) ^ 52565519823923889578 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 3391323859607992876 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 607693870796807972 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 57417279982440076 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 39278612 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_136443408093351935461 : Nat.Prime 136443408093351935461 := by
  apply lucas_primality 136443408093351935461 (6 : ZMod 136443408093351935461)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (43, 1), (17628347298882679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (43, 1), (17628347298882679, 1)] : List FactorBlock).map factorBlockValue).prod) = 136443408093351935461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_43
      · exact prime_oneHundredThirtyDX_17628347298882679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 136443408093351935461) ^ 68221704046675967730 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 136443408093351935461) ^ 45481136031117311820 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 136443408093351935461) ^ 27288681618670387092 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 136443408093351935461) ^ 3173102513798882220 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 136443408093351935461) ^ 7740 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_330381160624252944851 : Nat.Prime 330381160624252944851 := by
  apply lucas_primality 330381160624252944851 (2 : ZMod 330381160624252944851)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (42474407, 1), (22223881153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (42474407, 1), (22223881153, 1)] : List FactorBlock).map factorBlockValue).prod) = 330381160624252944851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_42474407
      · exact prime_oneHundredThirtyDX_22223881153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 330381160624252944851) ^ 165190580312126472425 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 330381160624252944851) ^ 66076232124850588970 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 330381160624252944851) ^ 47197308660607563550 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 330381160624252944851) ^ 7778358403550 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 330381160624252944851) ^ 14866042450 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_601135034269270369663 : Nat.Prime 601135034269270369663 := by
  apply lucas_primality 601135034269270369663 (3 : ZMod 601135034269270369663)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (101, 1), (142641539, 1), (2318099881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (101, 1), (142641539, 1), (2318099881, 1)] : List FactorBlock).map factorBlockValue).prod) = 601135034269270369663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_101
      · exact prime_oneHundredThirtyDX_142641539
      · exact prime_oneHundredThirtyDX_2318099881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 601135034269270369663) ^ 300567517134635184831 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 200378344756423456554 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 5951832022468023462 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 4214305583658 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 259322317902 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_828727030606824072991 : Nat.Prime 828727030606824072991 := by
  apply lucas_primality 828727030606824072991 (3 : ZMod 828727030606824072991)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (17, 1), (211, 1), (5351, 1), (16981, 1), (1345303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (17, 1), (211, 1), (5351, 1), (16981, 1), (1345303, 1)] : List FactorBlock).map factorBlockValue).prod) = 828727030606824072991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_211
      · exact prime_oneHundredThirtyDX_5351
      · exact prime_oneHundredThirtyDX_16981
      · exact prime_oneHundredThirtyDX_1345303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 828727030606824072991) ^ 414363515303412036495 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 828727030606824072991) ^ 276242343535608024330 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 828727030606824072991) ^ 165745406121364814598 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 828727030606824072991) ^ 118389575800974867570 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 828727030606824072991) ^ 48748648859224945470 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 828727030606824072991) ^ 3927616258800114090 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 828727030606824072991) ^ 154873300431101490 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 828727030606824072991) ^ 48803193605018790 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 828727030606824072991) ^ 616015150941330 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1081687868363620552253 : Nat.Prime 1081687868363620552253 := by
  apply lucas_primality 1081687868363620552253 (2 : ZMod 1081687868363620552253)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1081687868363620552253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_71
      · exact prime_oneHundredThirtyDX_199
      · exact prime_oneHundredThirtyDX_52864081
      · exact prime_oneHundredThirtyDX_362051087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1081687868363620552253) ^ 540843934181810276126 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 15235040399487613412 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 5435617428962917348 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 20461679232892 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 2987666401796 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1611381528507653776831 : Nat.Prime 1611381528507653776831 := by
  apply lucas_primality 1611381528507653776831 (6 : ZMod 1611381528507653776831)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (31, 1), (167, 1), (49807, 1), (18937205509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (31, 1), (167, 1), (49807, 1), (18937205509, 1)] : List FactorBlock).map factorBlockValue).prod) = 1611381528507653776831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_31
      · exact prime_oneHundredThirtyDX_167
      · exact prime_oneHundredThirtyDX_49807
      · exact prime_oneHundredThirtyDX_18937205509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1611381528507653776831) ^ 805690764253826888415 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1611381528507653776831) ^ 537127176169217925610 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1611381528507653776831) ^ 322276305701530755366 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1611381528507653776831) ^ 146489229864332161530 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1611381528507653776831) ^ 51980049306698508930 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1611381528507653776831) ^ 9648991188668585490 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1611381528507653776831) ^ 32352511263630690 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1611381528507653776831) ^ 85090776870 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_3044646295636344632269 : Nat.Prime 3044646295636344632269 := by
  apply lucas_primality 3044646295636344632269 (34 : ZMod 3044646295636344632269)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (23, 1), (47, 1), (33529869781467167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (23, 1), (47, 1), (33529869781467167, 1)] : List FactorBlock).map factorBlockValue).prod) = 3044646295636344632269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_23
      · exact prime_oneHundredThirtyDX_47
      · exact prime_oneHundredThirtyDX_33529869781467167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (34 : ZMod 3044646295636344632269) ^ 1522323147818172316134 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (34 : ZMod 3044646295636344632269) ^ 1014882098545448210756 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (34 : ZMod 3044646295636344632269) ^ 434949470805192090324 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (34 : ZMod 3044646295636344632269) ^ 132375925897232375316 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (34 : ZMod 3044646295636344632269) ^ 64779708417794566644 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (34 : ZMod 3044646295636344632269) ^ 90804 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_3289376689400252641763 : Nat.Prime 3289376689400252641763 := by
  apply lucas_primality 3289376689400252641763 (2 : ZMod 3289376689400252641763)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (11501317095805079167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (11501317095805079167, 1)] : List FactorBlock).map factorBlockValue).prod) = 3289376689400252641763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_11501317095805079167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3289376689400252641763) ^ 1644688344700126320881 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3289376689400252641763) ^ 299034244490932058342 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3289376689400252641763) ^ 253028976107711741674 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3289376689400252641763) ^ 286 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_3865523890840349272739 : Nat.Prime 3865523890840349272739 := by
  apply lucas_primality 3865523890840349272739 (2 : ZMod 3865523890840349272739)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (59, 1), (246305842413683527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (59, 1), (246305842413683527, 1)] : List FactorBlock).map factorBlockValue).prod) = 3865523890840349272739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_59
      · exact prime_oneHundredThirtyDX_246305842413683527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3865523890840349272739) ^ 1932761945420174636369 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3865523890840349272739) ^ 552217698691478467534 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3865523890840349272739) ^ 203448625833702593302 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3865523890840349272739) ^ 65517354082039818182 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3865523890840349272739) ^ 15694 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_8256808552939622841349 : Nat.Prime 8256808552939622841349 := by
  apply lucas_primality 8256808552939622841349 (10 : ZMod 8256808552939622841349)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (1069, 1), (120661, 1), (592712155459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (1069, 1), (120661, 1), (592712155459, 1)] : List FactorBlock).map factorBlockValue).prod) = 8256808552939622841349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_1069
      · exact prime_oneHundredThirtyDX_120661
      · exact prime_oneHundredThirtyDX_592712155459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 8256808552939622841349) ^ 4128404276469811420674 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (10 : ZMod 8256808552939622841349) ^ 2752269517646540947116 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (10 : ZMod 8256808552939622841349) ^ 7723862070102547092 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (10 : ZMod 8256808552939622841349) ^ 68429803772052468 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (10 : ZMod 8256808552939622841349) ^ 13930553772 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_12178585182545378529077 : Nat.Prime 12178585182545378529077 := by
  apply lucas_primality 12178585182545378529077 (2 : ZMod 12178585182545378529077)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3044646295636344632269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3044646295636344632269, 1)] : List FactorBlock).map factorBlockValue).prod) = 12178585182545378529077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3044646295636344632269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 12178585182545378529077) ^ 6089292591272689264538 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 12178585182545378529077) ^ 4 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_23850666232989622906939 : Nat.Prime 23850666232989622906939 := by
  apply lucas_primality 23850666232989622906939 (2 : ZMod 23850666232989622906939)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (1117, 1), (48749844113165203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (1117, 1), (48749844113165203, 1)] : List FactorBlock).map factorBlockValue).prod) = 23850666232989622906939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_73
      · exact prime_oneHundredThirtyDX_1117
      · exact prime_oneHundredThirtyDX_48749844113165203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23850666232989622906939) ^ 11925333116494811453469 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23850666232989622906939) ^ 7950222077663207635646 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23850666232989622906939) ^ 326721455246433190506 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23850666232989622906939) ^ 21352431721566358914 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23850666232989622906939) ^ 489246 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_74179768800836573759281 : Nat.Prime 74179768800836573759281 := by
  apply lucas_primality 74179768800836573759281 (7 : ZMod 74179768800836573759281)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (11, 1), (12073, 1), (2327374908725599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (11, 1), (12073, 1), (2327374908725599, 1)] : List FactorBlock).map factorBlockValue).prod) = 74179768800836573759281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_12073
      · exact prime_oneHundredThirtyDX_2327374908725599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 74179768800836573759281) ^ 37089884400418286879640 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 74179768800836573759281) ^ 24726589600278857919760 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 74179768800836573759281) ^ 14835953760167314751856 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 74179768800836573759281) ^ 6743615345530597614480 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 74179768800836573759281) ^ 6144269759035581360 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 74179768800836573759281) ^ 31872720 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_408111245176226541626333 : Nat.Prime 408111245176226541626333 := by
  apply lucas_primality 408111245176226541626333 (2 : ZMod 408111245176226541626333)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (239, 1), (349, 1), (2843, 1), (2939, 1), (3271, 1), (2632627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (239, 1), (349, 1), (2843, 1), (2939, 1), (3271, 1), (2632627, 1)] : List FactorBlock).map factorBlockValue).prod) = 408111245176226541626333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_239
      · exact prime_oneHundredThirtyDX_349
      · exact prime_oneHundredThirtyDX_2843
      · exact prime_oneHundredThirtyDX_2939
      · exact prime_oneHundredThirtyDX_3271
      · exact prime_oneHundredThirtyDX_2632627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 408111245176226541626333) ^ 204055622588113270813166 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 408111245176226541626333) ^ 24006543833895678919196 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 408111245176226541626333) ^ 1707578431699692642788 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 408111245176226541626333) ^ 1169373195347353987468 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 408111245176226541626333) ^ 143549505865714576724 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 408111245176226541626333) ^ 138860580189257074388 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 408111245176226541626333) ^ 124766507238222727492 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 408111245176226541626333) ^ 155020534688820916 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_936283580865327165810623 : Nat.Prime 936283580865327165810623 := by
  apply lucas_primality 936283580865327165810623 (5 : ZMod 936283580865327165810623)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (71, 1), (4657, 1), (38265826765415749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (71, 1), (4657, 1), (38265826765415749, 1)] : List FactorBlock).map factorBlockValue).prod) = 936283580865327165810623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_37
      · exact prime_oneHundredThirtyDX_71
      · exact prime_oneHundredThirtyDX_4657
      · exact prime_oneHundredThirtyDX_38265826765415749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 936283580865327165810623) ^ 468141790432663582905311 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 936283580865327165810623) ^ 25304961645008842319206 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 936283580865327165810623) ^ 13187092688244044588882 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 936283580865327165810623) ^ 201048653825494345246 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 936283580865327165810623) ^ 24467878 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1299403073472213758562043 : Nat.Prime 1299403073472213758562043 := by
  apply lucas_primality 1299403073472213758562043 (2 : ZMod 1299403073472213758562043)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (103, 1), (35637185932538362091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (103, 1), (35637185932538362091, 1)] : List FactorBlock).map factorBlockValue).prod) = 1299403073472213758562043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_59
      · exact prime_oneHundredThirtyDX_103
      · exact prime_oneHundredThirtyDX_35637185932538362091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1299403073472213758562043) ^ 649701536736106879281021 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299403073472213758562043) ^ 433134357824071252854014 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299403073472213758562043) ^ 22023780906308707772238 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299403073472213758562043) ^ 12615563820118580180214 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299403073472213758562043) ^ 36462 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1616562660356212627677907 : Nat.Prime 1616562660356212627677907 := by
  apply lucas_primality 1616562660356212627677907 (3 : ZMod 1616562660356212627677907)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (71171, 1), (921517, 1), (65207015611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (71171, 1), (921517, 1), (65207015611, 1)] : List FactorBlock).map factorBlockValue).prod) = 1616562660356212627677907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_71171
      · exact prime_oneHundredThirtyDX_921517
      · exact prime_oneHundredThirtyDX_65207015611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1616562660356212627677907) ^ 808281330178106313838953 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616562660356212627677907) ^ 538854220118737542559302 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616562660356212627677907) ^ 230937522908030375382558 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616562660356212627677907) ^ 22713783147015113286 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616562660356212627677907) ^ 1754240736043081818 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616562660356212627677907) ^ 24791238261846 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2933496744476684205456397 : Nat.Prime 2933496744476684205456397 := by
  apply lucas_primality 2933496744476684205456397 (2 : ZMod 2933496744476684205456397)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (101, 1), (19773913, 1), (2400049481591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (101, 1), (19773913, 1), (2400049481591, 1)] : List FactorBlock).map factorBlockValue).prod) = 2933496744476684205456397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_17
      · exact prime_oneHundredThirtyDX_101
      · exact prime_oneHundredThirtyDX_19773913
      · exact prime_oneHundredThirtyDX_2400049481591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2933496744476684205456397) ^ 1466748372238342102728198 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2933496744476684205456397) ^ 977832248158894735152132 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2933496744476684205456397) ^ 172558632028040247379788 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2933496744476684205456397) ^ 29044522222541427776796 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2933496744476684205456397) ^ 148351858556102892 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2933496744476684205456397) ^ 1222265110356 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_6861676634375057617593509 : Nat.Prime 6861676634375057617593509 := by
  apply lucas_primality 6861676634375057617593509 (2 : ZMod 6861676634375057617593509)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (210430769, 1), (8151940739207033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (210430769, 1), (8151940739207033, 1)] : List FactorBlock).map factorBlockValue).prod) = 6861676634375057617593509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_210430769
      · exact prime_oneHundredThirtyDX_8151940739207033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6861676634375057617593509) ^ 3430838317187528808796754 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6861676634375057617593509) ^ 32607762956828132 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6861676634375057617593509) ^ 841723076 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_7086296967742492303770437 : Nat.Prime 7086296967742492303770437 := by
  apply lucas_primality 7086296967742492303770437 (2 : ZMod 7086296967742492303770437)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1342519, 1), (1319589698123917111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1342519, 1), (1319589698123917111, 1)] : List FactorBlock).map factorBlockValue).prod) = 7086296967742492303770437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_1342519
      · exact prime_oneHundredThirtyDX_1319589698123917111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7086296967742492303770437) ^ 3543148483871246151885218 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7086296967742492303770437) ^ 5278358792495668444 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7086296967742492303770437) ^ 5370076 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_11218590871048679969085913 : Nat.Prime 11218590871048679969085913 := by
  apply lucas_primality 11218590871048679969085913 (5 : ZMod 11218590871048679969085913)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (47, 1), (241, 1), (9439, 1), (1997243, 1), (729682649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (47, 1), (241, 1), (9439, 1), (1997243, 1), (729682649, 1)] : List FactorBlock).map factorBlockValue).prod) = 11218590871048679969085913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_47
      · exact prime_oneHundredThirtyDX_241
      · exact prime_oneHundredThirtyDX_9439
      · exact prime_oneHundredThirtyDX_1997243
      · exact prime_oneHundredThirtyDX_729682649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11218590871048679969085913) ^ 5609295435524339984542956 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 3739530290349559989695304 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 238693422788269786576296 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 46550169589413609830232 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 1188535954131653773608 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 5617038523128472584 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 15374616467067288 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_12430822948347372660666209 : Nat.Prime 12430822948347372660666209 := by
  apply lucas_primality 12430822948347372660666209 (3 : ZMod 12430822948347372660666209)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (83, 1), (89, 1), (157, 1), (303997, 1), (1101825586553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (83, 1), (89, 1), (157, 1), (303997, 1), (1101825586553, 1)] : List FactorBlock).map factorBlockValue).prod) = 12430822948347372660666209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_83
      · exact prime_oneHundredThirtyDX_89
      · exact prime_oneHundredThirtyDX_157
      · exact prime_oneHundredThirtyDX_303997
      · exact prime_oneHundredThirtyDX_1101825586553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12430822948347372660666209) ^ 6215411474173686330333104 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 12430822948347372660666209) ^ 149768951184908104345376 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 12430822948347372660666209) ^ 139672167958959243378272 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 12430822948347372660666209) ^ 79177216231511927774944 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 12430822948347372660666209) ^ 40891268493923863264 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 12430822948347372660666209) ^ 11282024215136 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_27568555144998549879188701 : Nat.Prime 27568555144998549879188701 := by
  apply lucas_primality 27568555144998549879188701 (2 : ZMod 27568555144998549879188701)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (346417, 1), (88424436268679879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (346417, 1), (88424436268679879, 1)] : List FactorBlock).map factorBlockValue).prod) = 27568555144998549879188701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_346417
      · exact prime_oneHundredThirtyDX_88424436268679879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27568555144998549879188701) ^ 13784277572499274939594350 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27568555144998549879188701) ^ 9189518381666183293062900 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27568555144998549879188701) ^ 5513711028999709975837740 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27568555144998549879188701) ^ 79581992641811891100 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27568555144998549879188701) ^ 311775300 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_33010028980534131352336127 : Nat.Prime 33010028980534131352336127 := by
  apply lucas_primality 33010028980534131352336127 (5 : ZMod 33010028980534131352336127)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (127, 1), (2099093, 1), (3258568895629807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (127, 1), (2099093, 1), (3258568895629807, 1)] : List FactorBlock).map factorBlockValue).prod) = 33010028980534131352336127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_19
      · exact prime_oneHundredThirtyDX_127
      · exact prime_oneHundredThirtyDX_2099093
      · exact prime_oneHundredThirtyDX_3258568895629807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 33010028980534131352336127) ^ 16505014490267065676168063 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 33010028980534131352336127) ^ 1737369946343901650122954 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 33010028980534131352336127) ^ 259921488035701821671938 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 33010028980534131352336127) ^ 15725853490309448582 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 33010028980534131352336127) ^ 10130222818 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_69356811793035611722236917 : Nat.Prime 69356811793035611722236917 := by
  apply lucas_primality 69356811793035611722236917 (2 : ZMod 69356811793035611722236917)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (433, 1), (552388373, 1), (72493105517081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (433, 1), (552388373, 1), (72493105517081, 1)] : List FactorBlock).map factorBlockValue).prod) = 69356811793035611722236917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_433
      · exact prime_oneHundredThirtyDX_552388373
      · exact prime_oneHundredThirtyDX_72493105517081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 69356811793035611722236917) ^ 34678405896517805861118458 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 69356811793035611722236917) ^ 160177394441190789196852 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 69356811793035611722236917) ^ 125558058755584292 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 69356811793035611722236917) ^ 956736662036 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_84773687221934316368713187 : Nat.Prime 84773687221934316368713187 := by
  apply lucas_primality 84773687221934316368713187 (2 : ZMod 84773687221934316368713187)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (307, 1), (4717239199, 1), (944154591371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (307, 1), (4717239199, 1), (944154591371, 1)] : List FactorBlock).map factorBlockValue).prod) = 84773687221934316368713187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_31
      · exact prime_oneHundredThirtyDX_307
      · exact prime_oneHundredThirtyDX_4717239199
      · exact prime_oneHundredThirtyDX_944154591371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 84773687221934316368713187) ^ 42386843610967158184356593 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 84773687221934316368713187) ^ 2734635071675300528023006 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 84773687221934316368713187) ^ 276135788996528717813398 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 84773687221934316368713187) ^ 17971038492155614 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 84773687221934316368713187) ^ 89787930913766 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_119328179296092325758134323 : Nat.Prime 119328179296092325758134323 := by
  apply lucas_primality 119328179296092325758134323 (11 : ZMod 119328179296092325758134323)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (12718483, 1), (42262455447993997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (12718483, 1), (42262455447993997, 1)] : List FactorBlock).map factorBlockValue).prod) = 119328179296092325758134323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_37
      · exact prime_oneHundredThirtyDX_12718483
      · exact prime_oneHundredThirtyDX_42262455447993997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 119328179296092325758134323) ^ 59664089648046162879067161 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 119328179296092325758134323) ^ 39776059765364108586044774 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 119328179296092325758134323) ^ 3225085926921414209679306 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 119328179296092325758134323) ^ 9382265109454667334 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (11 : ZMod 119328179296092325758134323) ^ 2823503226 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_198060173883204788114016763 : Nat.Prime 198060173883204788114016763 := by
  apply lucas_primality 198060173883204788114016763 (3 : ZMod 198060173883204788114016763)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (33010028980534131352336127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (33010028980534131352336127, 1)] : List FactorBlock).map factorBlockValue).prod) = 198060173883204788114016763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_33010028980534131352336127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 198060173883204788114016763) ^ 99030086941602394057008381 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 198060173883204788114016763) ^ 66020057961068262704672254 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 198060173883204788114016763) ^ 6 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_256585467334502363232849763 : Nat.Prime 256585467334502363232849763 := by
  apply lucas_primality 256585467334502363232849763 (2 : ZMod 256585467334502363232849763)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (163, 1), (23850666232989622906939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (163, 1), (23850666232989622906939, 1)] : List FactorBlock).map factorBlockValue).prod) = 256585467334502363232849763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_163
      · exact prime_oneHundredThirtyDX_23850666232989622906939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256585467334502363232849763) ^ 128292733667251181616424881 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 256585467334502363232849763) ^ 85528489111500787744283254 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 256585467334502363232849763) ^ 23325951575863851202986342 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 256585467334502363232849763) ^ 1574143971377315111857974 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 256585467334502363232849763) ^ 10758 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_571355743246717158276866201 : Nat.Prime 571355743246717158276866201 := by
  apply lucas_primality 571355743246717158276866201 (3 : ZMod 571355743246717158276866201)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (7, 1), (408111245176226541626333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (7, 1), (408111245176226541626333, 1)] : List FactorBlock).map factorBlockValue).prod) = 571355743246717158276866201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_408111245176226541626333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 571355743246717158276866201) ^ 285677871623358579138433100 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 571355743246717158276866201) ^ 114271148649343431655373240 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 571355743246717158276866201) ^ 81622249035245308325266600 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 571355743246717158276866201) ^ 1400 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_909436064694478790393355077 : Nat.Prime 909436064694478790393355077 := by
  apply lucas_primality 909436064694478790393355077 (2 : ZMod 909436064694478790393355077)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4171314503, 1), (54505364198768423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4171314503, 1), (54505364198768423, 1)] : List FactorBlock).map factorBlockValue).prod) = 909436064694478790393355077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_4171314503
      · exact prime_oneHundredThirtyDX_54505364198768423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 909436064694478790393355077) ^ 454718032347239395196677538 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 909436064694478790393355077) ^ 218021456795073692 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 909436064694478790393355077) ^ 16685258012 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1348199078362867680495412351 : Nat.Prime 1348199078362867680495412351 := by
  apply lucas_primality 1348199078362867680495412351 (28 : ZMod 1348199078362867680495412351)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 2), (3391, 1), (820351907, 1), (26702345737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 2), (3391, 1), (820351907, 1), (26702345737, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348199078362867680495412351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_3391
      · exact prime_oneHundredThirtyDX_820351907
      · exact prime_oneHundredThirtyDX_26702345737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (28 : ZMod 1348199078362867680495412351) ^ 674099539181433840247706175 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (28 : ZMod 1348199078362867680495412351) ^ 449399692787622560165137450 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (28 : ZMod 1348199078362867680495412351) ^ 269639815672573536099082470 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (28 : ZMod 1348199078362867680495412351) ^ 122563552578442516408673850 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (28 : ZMod 1348199078362867680495412351) ^ 397581562477991058830850 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (28 : ZMod 1348199078362867680495412351) ^ 1643439927254131050 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (28 : ZMod 1348199078362867680495412351) ^ 50489911696961550 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1360130043658114297136964673 : Nat.Prime 1360130043658114297136964673 := by
  apply lucas_primality 1360130043658114297136964673 (5 : ZMod 1360130043658114297136964673)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (47, 1), (197, 1), (2820541, 1), (30139788084221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (47, 1), (197, 1), (2820541, 1), (30139788084221, 1)] : List FactorBlock).map factorBlockValue).prod) = 1360130043658114297136964673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_47
      · exact prime_oneHundredThirtyDX_197
      · exact prime_oneHundredThirtyDX_2820541
      · exact prime_oneHundredThirtyDX_30139788084221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1360130043658114297136964673) ^ 680065021829057148568482336 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1360130043658114297136964673) ^ 453376681219371432378988224 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1360130043658114297136964673) ^ 28938937099108814832701376 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1360130043658114297136964673) ^ 6904213419584336533690176 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1360130043658114297136964673) ^ 482223106722474268992 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1360130043658114297136964673) ^ 45127392397632 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1410043072783182711710798239 : Nat.Prime 1410043072783182711710798239 := by
  apply lucas_primality 1410043072783182711710798239 (6 : ZMod 1410043072783182711710798239)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (251, 1), (936283580865327165810623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (251, 1), (936283580865327165810623, 1)] : List FactorBlock).map factorBlockValue).prod) = 1410043072783182711710798239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_251
      · exact prime_oneHundredThirtyDX_936283580865327165810623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1410043072783182711710798239) ^ 705021536391591355855399119 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1410043072783182711710798239) ^ 470014357594394237236932746 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1410043072783182711710798239) ^ 5617701485191962994863738 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1410043072783182711710798239) ^ 1506 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_1436399018068849678284831851 : Nat.Prime 1436399018068849678284831851 := by
  apply lucas_primality 1436399018068849678284831851 (2 : ZMod 1436399018068849678284831851)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (929, 1), (8369, 1), (14713, 1), (509939, 1), (492488791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (929, 1), (8369, 1), (14713, 1), (509939, 1), (492488791, 1)] : List FactorBlock).map factorBlockValue).prod) = 1436399018068849678284831851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_929
      · exact prime_oneHundredThirtyDX_8369
      · exact prime_oneHundredThirtyDX_14713
      · exact prime_oneHundredThirtyDX_509939
      · exact prime_oneHundredThirtyDX_492488791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1436399018068849678284831851) ^ 718199509034424839142415925 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1436399018068849678284831851) ^ 287279803613769935656966370 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1436399018068849678284831851) ^ 1546177629783476510532650 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1436399018068849678284831851) ^ 171633291679872108768650 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1436399018068849678284831851) ^ 97627881334116065947450 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1436399018068849678284831851) ^ 2816805574919450519150 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1436399018068849678284831851) ^ 2916612609907805350 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2134648540741207160784402889 : Nat.Prime 2134648540741207160784402889 := by
  apply lucas_primality 2134648540741207160784402889 (7 : ZMod 2134648540741207160784402889)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (113, 1), (197, 1), (2820541, 1), (30139788084221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (113, 1), (197, 1), (2820541, 1), (30139788084221, 1)] : List FactorBlock).map factorBlockValue).prod) = 2134648540741207160784402889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_47
      · exact prime_oneHundredThirtyDX_113
      · exact prime_oneHundredThirtyDX_197
      · exact prime_oneHundredThirtyDX_2820541
      · exact prime_oneHundredThirtyDX_30139788084221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2134648540741207160784402889) ^ 1067324270370603580392201444 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2134648540741207160784402889) ^ 711549513580402386928134296 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2134648540741207160784402889) ^ 45418054058323556612434104 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2134648540741207160784402889) ^ 18890695050807143015791176 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2134648540741207160784402889) ^ 10835779394625417059819304 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2134648540741207160784402889) ^ 756822375828327672168 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2134648540741207160784402889) ^ 70824935290728 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2401479608333858055882453251 : Nat.Prime 2401479608333858055882453251 := by
  apply lucas_primality 2401479608333858055882453251 (6 : ZMod 2401479608333858055882453251)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (13, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (13, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 2401479608333858055882453251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_13
      · exact prime_oneHundredThirtyDX_171401
      · exact prime_oneHundredThirtyDX_714027719
      · exact prime_oneHundredThirtyDX_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2401479608333858055882453251) ^ 1200739804166929027941226625 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2401479608333858055882453251) ^ 480295921666771611176490650 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2401479608333858055882453251) ^ 184729200641066004298650250 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2401479608333858055882453251) ^ 14010884465865765403250 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2401479608333858055882453251) ^ 3363286248462656750 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2401479608333858055882453251) ^ 397751461459036750 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_2604994829379100264008084883 : Nat.Prime 2604994829379100264008084883 := by
  apply lucas_primality 2604994829379100264008084883 (5 : ZMod 2604994829379100264008084883)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (61, 1), (631, 1), (1611381528507653776831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (61, 1), (631, 1), (1611381528507653776831, 1)] : List FactorBlock).map factorBlockValue).prod) = 2604994829379100264008084883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_61
      · exact prime_oneHundredThirtyDX_631
      · exact prime_oneHundredThirtyDX_1611381528507653776831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2604994829379100264008084883) ^ 1302497414689550132004042441 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 2604994829379100264008084883) ^ 868331609793033421336028294 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 2604994829379100264008084883) ^ 372142118482728609144012126 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 2604994829379100264008084883) ^ 42704833268509840393575162 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 2604994829379100264008084883) ^ 4128359476036608976241022 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 2604994829379100264008084883) ^ 1616622 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_4802959216667716111764906503 : Nat.Prime 4802959216667716111764906503 := by
  apply lucas_primality 4802959216667716111764906503 (5 : ZMod 4802959216667716111764906503)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2401479608333858055882453251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2401479608333858055882453251, 1)] : List FactorBlock).map factorBlockValue).prod) = 4802959216667716111764906503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_2401479608333858055882453251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 4802959216667716111764906503) ^ 2401479608333858055882453251 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 4802959216667716111764906503) ^ 2 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_38423673733341728894119252003 : Nat.Prime 38423673733341728894119252003 := by
  apply lucas_primality 38423673733341728894119252003 (3 : ZMod 38423673733341728894119252003)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2134648540741207160784402889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2134648540741207160784402889, 1)] : List FactorBlock).map factorBlockValue).prod) = 38423673733341728894119252003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_2134648540741207160784402889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 38423673733341728894119252003) ^ 19211836866670864447059626001 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 38423673733341728894119252003) ^ 12807891244447242964706417334 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (3 : ZMod 38423673733341728894119252003) ^ 18 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_38423673733341728894119252007 : Nat.Prime 38423673733341728894119252007 := by
  apply lucas_primality 38423673733341728894119252007 (5 : ZMod 38423673733341728894119252007)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (119328179296092325758134323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (119328179296092325758134323, 1)] : List FactorBlock).map factorBlockValue).prod) = 38423673733341728894119252007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_7
      · exact prime_oneHundredThirtyDX_23
      · exact prime_oneHundredThirtyDX_119328179296092325758134323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 38423673733341728894119252007) ^ 19211836866670864447059626003 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 38423673733341728894119252007) ^ 5489096247620246984874178858 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 38423673733341728894119252007) ^ 1670594510145292560613880522 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (5 : ZMod 38423673733341728894119252007) ^ 322 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_38423673733341728894119252009 : Nat.Prime 38423673733341728894119252009 := by
  apply lucas_primality 38423673733341728894119252009 (7 : ZMod 38423673733341728894119252009)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (2339, 1), (583417, 1), (23683529, 1), (4503386711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (2339, 1), (583417, 1), (23683529, 1), (4503386711, 1)] : List FactorBlock).map factorBlockValue).prod) = 38423673733341728894119252009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_3
      · exact prime_oneHundredThirtyDX_11
      · exact prime_oneHundredThirtyDX_2339
      · exact prime_oneHundredThirtyDX_583417
      · exact prime_oneHundredThirtyDX_23683529
      · exact prime_oneHundredThirtyDX_4503386711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 38423673733341728894119252009) ^ 19211836866670864447059626004 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 38423673733341728894119252009) ^ 12807891244447242964706417336 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 38423673733341728894119252009) ^ 3493061248485611717647204728 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 38423673733341728894119252009) ^ 16427393644010999954732472 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 38423673733341728894119252009) ^ 65859708807494003250024 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 38423673733341728894119252009) ^ 1622379575836934136552 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (7 : ZMod 38423673733341728894119252009) ^ 8532172828837423128 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyDX_153694694933366915576477008061 : Nat.Prime 153694694933366915576477008061 := by
  apply lucas_primality 153694694933366915576477008061 (2 : ZMod 153694694933366915576477008061)
  · rw [← oneHundredThirtyDXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (307, 1), (8302403, 1), (3014995691311940443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (307, 1), (8302403, 1), (3014995691311940443, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyDX_2
      · exact prime_oneHundredThirtyDX_5
      · exact prime_oneHundredThirtyDX_307
      · exact prime_oneHundredThirtyDX_8302403
      · exact prime_oneHundredThirtyDX_3014995691311940443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 153694694933366915576477008061) ^ 76847347466683457788238504030 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 153694694933366915576477008061) ^ 30738938986673383115295401612 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 153694694933366915576477008061) ^ 500634185450706565395690580 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 153694694933366915576477008061) ^ 18512073544655314320020 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide
    · change (2 : ZMod 153694694933366915576477008061) ^ 50976754420 ≠ 1
      rw [← oneHundredThirtyDXFastPow_eq_pow]
      decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008000 : Nat.totient 153694694933366915576477008000 = 56748479260082249026990080000 := by
  rw [← show ((([(2, 7), (5, 3), (13, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_13, prime_oneHundredThirtyDX_171401, prime_oneHundredThirtyDX_714027719, prime_oneHundredThirtyDX_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008001 : Nat.totient 153694694933366915576477008001 = 146379587958209594046580885440 := by
  rw [← show ((([(23, 1), (283, 1), (2267, 1), (3011, 1), (3459253030453840597, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_23, prime_oneHundredThirtyDX_283, prime_oneHundredThirtyDX_2267, prime_oneHundredThirtyDX_3011, prime_oneHundredThirtyDX_3459253030453840597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008002 : Nat.totient 153694694933366915576477008002 = 51231548464171865979573781872 := by
  rw [← show ((([(2, 1), (3, 1), (3102383, 1), (8256808552939622841349, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_3102383, prime_oneHundredThirtyDX_8256808552939622841349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008003 : Nat.totient 153694694933366915576477008003 = 131270007295949198690867667840 := by
  rw [← show ((([(7, 1), (293, 1), (7027, 1), (346226141, 1), (30800900101879, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_7, prime_oneHundredThirtyDX_293, prime_oneHundredThirtyDX_7027, prime_oneHundredThirtyDX_346226141, prime_oneHundredThirtyDX_30800900101879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008004 : Nat.totient 153694694933366915576477008004 = 76847347428642159074991512064 := by
  rw [← show ((([(2, 2), (2020103153, 1), (19020649354603392817, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_2020103153, prime_oneHundredThirtyDX_19020649354603392817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008005 : Nat.totient 153694694933366915576477008005 = 76848215002901339694633058304 := by
  rw [← show ((([(3, 1), (5, 1), (17, 1), (257, 1), (251897, 1), (9310276483619584019, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_17, prime_oneHundredThirtyDX_257, prime_oneHundredThirtyDX_251897, prime_oneHundredThirtyDX_9310276483619584019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008006 : Nat.totient 153694694933366915576477008006 = 76847335288098275242853664888 := by
  rw [← show ((([(2, 1), (6310039, 1), (12178585182545378529077, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_6310039, prime_oneHundredThirtyDX_12178585182545378529077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008007 : Nat.totient 153694694933366915576477008007 = 152661475947614663232767608320 := by
  rw [← show ((([(149, 1), (89231, 1), (1697662997, 1), (6809345431249, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_149, prime_oneHundredThirtyDX_89231, prime_oneHundredThirtyDX_1697662997, prime_oneHundredThirtyDX_6809345431249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008008 : Nat.totient 153694694933366915576477008008 = 51231564977788971858825669312 := by
  rw [← show ((([(2, 3), (3, 2), (2134648540741207160784402889, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_2134648540741207160784402889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008009 : Nat.totient 153694694933366915576477008009 = 153694694933302248400257453204 := by
  rw [← show ((([(2376790715983, 1), (64664799428838823, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2376790715983, prime_oneHundredThirtyDX_64664799428838823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008010 : Nat.totient 153694694933366915576477008010 = 47748807158513766903664035840 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (11, 1), (317, 1), (9719, 1), (6998309863, 1), (9257508937, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_7, prime_oneHundredThirtyDX_11, prime_oneHundredThirtyDX_317, prime_oneHundredThirtyDX_9719, prime_oneHundredThirtyDX_6998309863, prime_oneHundredThirtyDX_9257508937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008011 : Nat.totient 153694694933366915576477008011 = 98552645010527880573512294400 := by
  rw [← show ((([(3, 1), (41, 1), (71, 1), (28649, 1), (5848541759, 1), (105036043537, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_41, prime_oneHundredThirtyDX_71, prime_oneHundredThirtyDX_28649, prime_oneHundredThirtyDX_5848541759, prime_oneHundredThirtyDX_105036043537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008012 : Nat.totient 153694694933366915576477008012 = 76847347466683457788238504004 := by
  rw [← show ((([(2, 2), (38423673733341728894119252003, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_38423673733341728894119252003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008013 : Nat.totient 153694694933366915576477008013 = 141872026092338691301363391856 := by
  rw [← show ((([(13, 2), (909436064694478790393355077, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_13, prime_oneHundredThirtyDX_909436064694478790393355077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008014 : Nat.totient 153694694933366915576477008014 = 48535166821063236497834844600 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (1348199078362867680495412351, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_19, prime_oneHundredThirtyDX_1348199078362867680495412351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008015 : Nat.totient 153694694933366915576477008015 = 122945731864815281199715123200 := by
  rw [← show ((([(5, 1), (14051, 1), (172313, 1), (237467, 1), (3638827, 1), (14692609, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_14051, prime_oneHundredThirtyDX_172313, prime_oneHundredThirtyDX_237467, prime_oneHundredThirtyDX_3638827, prime_oneHundredThirtyDX_14692609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008016 : Nat.totient 153694694933366915576477008016 = 74368400766437618827861824000 := by
  rw [← show ((([(2, 4), (31, 1), (9568542161, 1), (32384069730307111, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_31, prime_oneHundredThirtyDX_9568542161, prime_oneHundredThirtyDX_32384069730307111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008017 : Nat.totient 153694694933366915576477008017 = 86033757606489228784709260800 := by
  rw [← show ((([(3, 3), (7, 1), (53, 1), (647, 1), (56783, 1), (417636636125115401, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_7, prime_oneHundredThirtyDX_53, prime_oneHundredThirtyDX_647, prime_oneHundredThirtyDX_56783, prime_oneHundredThirtyDX_417636636125115401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008018 : Nat.totient 153694694933366915576477008018 = 76829709791978965947015982080 := by
  rw [← show ((([(2, 1), (4357, 1), (275384832181, 1), (64047370672577, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_4357, prime_oneHundredThirtyDX_275384832181, prime_oneHundredThirtyDX_64047370672577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008019 : Nat.totient 153694694933366915576477008019 = 144548888986711319617449919872 := by
  rw [← show ((([(29, 1), (43, 1), (367, 1), (50170357, 1), (6693899198418583, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_29, prime_oneHundredThirtyDX_43, prime_oneHundredThirtyDX_367, prime_oneHundredThirtyDX_50170357, prime_oneHundredThirtyDX_6693899198418583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008020 : Nat.totient 153694694933366915576477008020 = 40690393663236518095422341760 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (139, 1), (104050223, 1), (177112743868002511, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_139, prime_oneHundredThirtyDX_104050223, prime_oneHundredThirtyDX_177112743868002511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008021 : Nat.totient 153694694933366915576477008021 = 139399765297532033443287937920 := by
  rw [← show ((([(11, 2), (433, 1), (2933496744476684205456397, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_11, prime_oneHundredThirtyDX_433, prime_oneHundredThirtyDX_2933496744476684205456397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008022 : Nat.totient 153694694933366915576477008022 = 71850626078467216213094400000 := by
  rw [← show ((([(2, 1), (17, 2), (263, 1), (401, 1), (3517, 1), (86389, 1), (216371, 1), (38353151, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_17, prime_oneHundredThirtyDX_263, prime_oneHundredThirtyDX_401, prime_oneHundredThirtyDX_3517, prime_oneHundredThirtyDX_86389, prime_oneHundredThirtyDX_216371, prime_oneHundredThirtyDX_38353151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008023 : Nat.totient 153694694933366915576477008023 = 102460612142876961114890452800 := by
  rw [← show ((([(3, 1), (48823, 1), (244451, 1), (4292609106502437817, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_48823, prime_oneHundredThirtyDX_244451, prime_oneHundredThirtyDX_4292609106502437817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008024 : Nat.totient 153694694933366915576477008024 = 63005278668336748000294922016 := by
  rw [← show ((([(2, 3), (7, 1), (23, 1), (119328179296092325758134323, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_7, prime_oneHundredThirtyDX_23, prime_oneHundredThirtyDX_119328179296092325758134323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008025 : Nat.totient 153694694933366915576477008025 = 122923424693486408208627972240 := by
  rw [← show ((([(5, 2), (3803, 1), (1616562660356212627677907, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_3803, prime_oneHundredThirtyDX_1616562660356212627677907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008026 : Nat.totient 153694694933366915576477008026 = 47290597482586374919730982528 := by
  rw [← show ((([(2, 1), (3, 2), (13, 1), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_13, prime_oneHundredThirtyDX_607213, prime_oneHundredThirtyDX_1081687868363620552253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008027 : Nat.totient 153694694933366915576477008027 = 153693008746040041037191088832 := by
  rw [← show ((([(91397, 1), (33624103, 1), (50012231077210697, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_91397, prime_oneHundredThirtyDX_33624103, prime_oneHundredThirtyDX_50012231077210697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008028 : Nat.totient 153694694933366915576477008028 = 76847347466683457788238504012 := by
  rw [← show ((([(2, 2), (38423673733341728894119252007, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_38423673733341728894119252007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008029 : Nat.totient 153694694933366915576477008029 = 102268243213477023736555937280 := by
  rw [← show ((([(3, 1), (733, 1), (1861, 1), (868423, 1), (43246997146607257, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_733, prime_oneHundredThirtyDX_1861, prime_oneHundredThirtyDX_868423, prime_oneHundredThirtyDX_43246997146607257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008030 : Nat.totient 153694694933366915576477008030 = 60169454500621025853093993984 := by
  rw [← show ((([(2, 1), (5, 1), (47, 1), (160183, 1), (7631857, 1), (267494201311979, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_47, prime_oneHundredThirtyDX_160183, prime_oneHundredThirtyDX_7631857, prime_oneHundredThirtyDX_267494201311979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008031 : Nat.totient 153694694933366915576477008031 = 128177815079564686349494337232 := by
  rw [← show ((([(7, 2), (37, 1), (84773687221934316368713187, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_7, prime_oneHundredThirtyDX_37, prime_oneHundredThirtyDX_84773687221934316368713187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008032 : Nat.totient 153694694933366915576477008032 = 46554156215678100432483532800 := by
  rw [← show ((([(2, 5), (3, 1), (11, 1), (2339, 1), (583417, 1), (23683529, 1), (4503386711, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_11, prime_oneHundredThirtyDX_2339, prime_oneHundredThirtyDX_583417, prime_oneHundredThirtyDX_23683529, prime_oneHundredThirtyDX_4503386711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008033 : Nat.totient 153694694933366915576477008033 = 145422933237089557415592595200 := by
  rw [← show ((([(19, 1), (829, 1), (21061, 1), (6572983, 1), (70487035972141, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_19, prime_oneHundredThirtyDX_829, prime_oneHundredThirtyDX_21061, prime_oneHundredThirtyDX_6572983, prime_oneHundredThirtyDX_70487035972141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008034 : Nat.totient 153694694933366915576477008034 = 76600230811882139342063126400 := by
  rw [← show ((([(2, 1), (311, 1), (4015841, 1), (61530718043549270167, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_311, prime_oneHundredThirtyDX_4015841, prime_oneHundredThirtyDX_61530718043549270167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008035 : Nat.totient 153694694933366915576477008035 = 81964535019980405308673149440 := by
  rw [← show ((([(3, 2), (5, 1), (14107, 1), (517721, 1), (467644591344983909, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_14107, prime_oneHundredThirtyDX_517721, prime_oneHundredThirtyDX_467644591344983909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008036 : Nat.totient 153694694933366915576477008036 = 76847347466683457788238504016 := by
  rw [← show ((([(2, 2), (38423673733341728894119252009, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_38423673733341728894119252009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008037 : Nat.totient 153694694933366915576477008037 = 153438109466032413213244157676 := by
  rw [← show ((([(599, 1), (256585467334502363232849763, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_599, prime_oneHundredThirtyDX_256585467334502363232849763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008038 : Nat.totient 153694694933366915576477008038 = 42393514357202161683865104000 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (59, 1), (61, 1), (631, 1), (1611381528507653776831, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_7, prime_oneHundredThirtyDX_59, prime_oneHundredThirtyDX_61, prime_oneHundredThirtyDX_631, prime_oneHundredThirtyDX_1611381528507653776831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008039 : Nat.totient 153694694933366915576477008039 = 133270323702961652260482723840 := by
  rw [← show ((([(13, 1), (17, 1), (521, 1), (23096547757, 1), (57793874370247, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_13, prime_oneHundredThirtyDX_17, prime_oneHundredThirtyDX_521, prime_oneHundredThirtyDX_23096547757, prime_oneHundredThirtyDX_57793874370247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008040 : Nat.totient 153694694933366915576477008040 = 61477877973344387747660439552 := by
  rw [← show ((([(2, 3), (5, 1), (33312673606897, 1), (115342509540833, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_33312673606897, prime_oneHundredThirtyDX_115342509540833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008041 : Nat.totient 153694694933366915576477008041 = 102463129951470305384666059872 := by
  rw [← show ((([(3, 1), (24944535739, 1), (2053819141548103673, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_24944535739, prime_oneHundredThirtyDX_2053819141548103673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008042 : Nat.totient 153694694933366915576477008042 = 76847347409146870603594327500 := by
  rw [← show ((([(2, 1), (1335625751, 1), (57536587183308550771, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_1335625751, prime_oneHundredThirtyDX_57536587183308550771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008043 : Nat.totient 153694694933366915576477008043 = 139644503414760847204447200000 := by
  rw [← show ((([(11, 1), (1801, 1), (429223, 1), (3431221, 1), (5267697195811, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_11, prime_oneHundredThirtyDX_1801, prime_oneHundredThirtyDX_429223, prime_oneHundredThirtyDX_3431221, prime_oneHundredThirtyDX_5267697195811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008044 : Nat.totient 153694694933366915576477008044 = 51207591197268071558582722560 := by
  rw [← show ((([(2, 2), (3, 3), (2137, 1), (270871009, 1), (2458487894036921, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_2137, prime_oneHundredThirtyDX_270871009, prime_oneHundredThirtyDX_2458487894036921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008045 : Nat.totient 153694694933366915576477008045 = 104769309881203045128403776000 := by
  rw [← show ((([(5, 1), (7, 1), (191, 1), (1831, 1), (8521, 1), (1473596414167950607, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_7, prime_oneHundredThirtyDX_191, prime_oneHundredThirtyDX_1831, prime_oneHundredThirtyDX_8521, prime_oneHundredThirtyDX_1473596414167950607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008046 : Nat.totient 153694694933366915576477008046 = 75667067259409474746794311680 := by
  rw [← show ((([(2, 1), (103, 1), (193, 1), (2477, 1), (8147, 1), (2557111, 1), (74913664993, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_103, prime_oneHundredThirtyDX_193, prime_oneHundredThirtyDX_2477, prime_oneHundredThirtyDX_8147, prime_oneHundredThirtyDX_2557111, prime_oneHundredThirtyDX_74913664993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008047 : Nat.totient 153694694933366915576477008047 = 92498878932916737952325952000 := by
  rw [← show ((([(3, 1), (23, 1), (31, 1), (67, 1), (101, 1), (13037, 1), (814468421742501887, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_23, prime_oneHundredThirtyDX_31, prime_oneHundredThirtyDX_67, prime_oneHundredThirtyDX_101, prime_oneHundredThirtyDX_13037, prime_oneHundredThirtyDX_814468421742501887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008048 : Nat.totient 153694694933366915576477008048 = 74145709660406083572207104000 := by
  rw [← show ((([(2, 4), (29, 1), (1481, 1), (45497, 1), (4915900423864514951, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_29, prime_oneHundredThirtyDX_1481, prime_oneHundredThirtyDX_45497, prime_oneHundredThirtyDX_4915900423864514951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008049 : Nat.totient 153694694933366915576477008049 = 152334564889708801279340043264 := by
  rw [← show ((([(113, 1), (1360130043658114297136964673, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_113, prime_oneHundredThirtyDX_1360130043658114297136964673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008050 : Nat.totient 153694694933366915576477008050 = 40985251865129411303192115840 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (349996873, 1), (2927544154246713619, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_349996873, prime_oneHundredThirtyDX_2927544154246713619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008051 : Nat.totient 153694694933366915576477008051 = 152284651860583732864766209704 := by
  rw [← show ((([(109, 1), (1410043072783182711710798239, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_109, prime_oneHundredThirtyDX_1410043072783182711710798239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008052 : Nat.totient 153694694933366915576477008052 = 56055685995952088160597442560 := by
  rw [← show ((([(2, 2), (7, 1), (13, 1), (19, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_7, prime_oneHundredThirtyDX_13, prime_oneHundredThirtyDX_19, prime_oneHundredThirtyDX_41, prime_oneHundredThirtyDX_397, prime_oneHundredThirtyDX_13617913, prime_oneHundredThirtyDX_100257985466497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008053 : Nat.totient 153694694933366915576477008053 = 102463129136917495156788768960 := by
  rw [← show ((([(3, 2), (125159497, 1), (136443408093351935461, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_125159497, prime_oneHundredThirtyDX_136443408093351935461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008054 : Nat.totient 153694694933366915576477008054 = 68425502904875389345002777600 := by
  rw [← show ((([(2, 1), (11, 1), (79, 1), (167, 1), (853, 1), (1181, 1), (525646413082499593, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_11, prime_oneHundredThirtyDX_79, prime_oneHundredThirtyDX_167, prime_oneHundredThirtyDX_853, prime_oneHundredThirtyDX_1181, prime_oneHundredThirtyDX_525646413082499593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008055 : Nat.totient 153694694933366915576477008055 = 121217169930382422731748888576 := by
  rw [← show ((([(5, 1), (73, 1), (2293, 1), (88423, 1), (59899309, 1), (34671681157, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_73, prime_oneHundredThirtyDX_2293, prime_oneHundredThirtyDX_88423, prime_oneHundredThirtyDX_59899309, prime_oneHundredThirtyDX_34671681157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008056 : Nat.totient 153694694933366915576477008056 = 48217943508374303421338677248 := by
  rw [← show ((([(2, 3), (3, 1), (17, 1), (362765197849, 1), (1038420129311893, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_17, prime_oneHundredThirtyDX_362765197849, prime_oneHundredThirtyDX_1038420129311893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008057 : Nat.totient 153694694933366915576477008057 = 152258295915298065898192176100 := by
  rw [← show ((([(107, 1), (1436399018068849678284831851, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_107, prime_oneHundredThirtyDX_1436399018068849678284831851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008058 : Nat.totient 153694694933366915576477008058 = 76757357006188330138276896000 := by
  rw [← show ((([(2, 1), (1381, 1), (2459, 1), (37181, 1), (111043, 1), (215191, 1), (25470667, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_1381, prime_oneHundredThirtyDX_2459, prime_oneHundredThirtyDX_37181, prime_oneHundredThirtyDX_111043, prime_oneHundredThirtyDX_215191, prime_oneHundredThirtyDX_25470667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008059 : Nat.totient 153694694933366915576477008059 = 87769159682874856170317383680 := by
  rw [← show ((([(3, 1), (7, 1), (2543, 1), (4019, 1), (938742491, 1), (762831713857, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_7, prime_oneHundredThirtyDX_2543, prime_oneHundredThirtyDX_4019, prime_oneHundredThirtyDX_938742491, prime_oneHundredThirtyDX_762831713857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008060 : Nat.totient 153694694933366915576477008060 = 61277616918457031252478042432 := by
  rw [← show ((([(2, 2), (5, 1), (307, 1), (8302403, 1), (3014995691311940443, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_307, prime_oneHundredThirtyDX_8302403, prime_oneHundredThirtyDX_3014995691311940443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008061 : Nat.totient 153694694933366915576477008061 = 153694694933366915576477008060 := by
  rw [← show ((([(153694694933366915576477008061, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_153694694933366915576477008061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008062 : Nat.totient 153694694933366915576477008062 = 50034936972703211126052799680 := by
  rw [← show ((([(2, 1), (3, 2), (43, 1), (9631, 1), (95225759, 1), (216517044774197, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_43, prime_oneHundredThirtyDX_9631, prime_oneHundredThirtyDX_95225759, prime_oneHundredThirtyDX_216517044774197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008063 : Nat.totient 153694694933366915576477008063 = 153681537266927544410008704000 := by
  rw [← show ((([(11681, 1), (267597212401, 1), (49169667142223, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_11681, prime_oneHundredThirtyDX_267597212401, prime_oneHundredThirtyDX_49169667142223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008064 : Nat.totient 153694694933366915576477008064 = 76847347466683457788238504000 := by
  rw [← show ((([(2, 6), (2401479608333858055882453251, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_2401479608333858055882453251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008065 : Nat.totient 153694694933366915576477008065 = 68636244959581979356406784000 := by
  rw [← show ((([(3, 1), (5, 1), (11, 1), (13, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_11, prime_oneHundredThirtyDX_13, prime_oneHundredThirtyDX_461, prime_oneHundredThirtyDX_69997, prime_oneHundredThirtyDX_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008066 : Nat.totient 153694694933366915576477008066 = 65869154971204404862743217776 := by
  rw [← show ((([(2, 1), (7, 1), (276114607397, 1), (39759549843214027, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_7, prime_oneHundredThirtyDX_276114607397, prime_oneHundredThirtyDX_39759549843214027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008067 : Nat.totient 153694694933366915576477008067 = 153548187360098996452320748800 := by
  rw [← show ((([(1399, 1), (4201, 1), (1798523, 1), (86482499, 1), (168129629, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_1399, prime_oneHundredThirtyDX_4201, prime_oneHundredThirtyDX_1798523, prime_oneHundredThirtyDX_86482499, prime_oneHundredThirtyDX_168129629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008068 : Nat.totient 153694694933366915576477008068 = 49841870950128967124964950016 := by
  rw [← show ((([(2, 2), (3, 1), (37, 1), (9857, 1), (388344499, 1), (90430304443429, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_37, prime_oneHundredThirtyDX_9857, prime_oneHundredThirtyDX_388344499, prime_oneHundredThirtyDX_90430304443429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008069 : Nat.totient 153694694933366915576477008069 = 153123339190120198418200141600 := by
  rw [← show ((([(269, 1), (571355743246717158276866201, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_269, prime_oneHundredThirtyDX_571355743246717158276866201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008070 : Nat.totient 153694694933366915576477008070 = 57694918757531316786648634368 := by
  rw [← show ((([(2, 1), (5, 1), (23, 1), (53, 1), (119929, 1), (105131039647847779157, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_23, prime_oneHundredThirtyDX_53, prime_oneHundredThirtyDX_119929, prime_oneHundredThirtyDX_105131039647847779157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008071 : Nat.totient 153694694933366915576477008071 = 96991476200031041639039030400 := by
  rw [← show ((([(3, 4), (19, 1), (1231, 1), (37574699, 1), (2159069857027081, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_19, prime_oneHundredThirtyDX_1231, prime_oneHundredThirtyDX_37574699, prime_oneHundredThirtyDX_2159069857027081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008072 : Nat.totient 153694694933366915576477008072 = 76569920219511315341349555264 := by
  rw [← show ((([(2, 3), (277, 1), (69356811793035611722236917, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_277, prime_oneHundredThirtyDX_69356811793035611722236917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008073 : Nat.totient 153694694933366915576477008073 = 123303974675065843933247201280 := by
  rw [← show ((([(7, 1), (17, 1), (181, 1), (148186273, 1), (48153223549512259, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_7, prime_oneHundredThirtyDX_17, prime_oneHundredThirtyDX_181, prime_oneHundredThirtyDX_148186273, prime_oneHundredThirtyDX_48153223549512259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008074 : Nat.totient 153694694933366915576477008074 = 50945237501884678049992790000 := by
  rw [← show ((([(2, 1), (3, 1), (179, 1), (433151, 1), (330381160624252944851, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_179, prime_oneHundredThirtyDX_433151, prime_oneHundredThirtyDX_330381160624252944851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008075 : Nat.totient 153694694933366915576477008075 = 122404384843793561463597828000 := by
  rw [← show ((([(5, 2), (223, 1), (27568555144998549879188701, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_223, prime_oneHundredThirtyDX_27568555144998549879188701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008076 : Nat.totient 153694694933366915576477008076 = 69612608510745286899730764800 := by
  rw [← show ((([(2, 2), (11, 1), (281, 1), (12430822948347372660666209, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_11, prime_oneHundredThirtyDX_281, prime_oneHundredThirtyDX_12430822948347372660666209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008077 : Nat.totient 153694694933366915576477008077 = 96824890253432416083304674560 := by
  rw [← show ((([(3, 1), (29, 1), (47, 1), (1399271, 1), (1439927, 1), (18655180611029, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_29, prime_oneHundredThirtyDX_47, prime_oneHundredThirtyDX_1399271, prime_oneHundredThirtyDX_1439927, prime_oneHundredThirtyDX_18655180611029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008078 : Nat.totient 153694694933366915576477008078 = 68647735486737664858464353280 := by
  rw [← show ((([(2, 1), (13, 1), (31, 1), (3599009, 1), (52983531609217552957, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_13, prime_oneHundredThirtyDX_31, prime_oneHundredThirtyDX_3599009, prime_oneHundredThirtyDX_52983531609217552957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008079 : Nat.totient 153694694933366915576477008079 = 151837311304746401729526784800 := by
  rw [← show ((([(83, 2), (26921, 1), (828727030606824072991, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_83, prime_oneHundredThirtyDX_26921, prime_oneHundredThirtyDX_828727030606824072991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008080 : Nat.totient 153694694933366915576477008080 = 35125368431853233306875350528 := by
  rw [← show ((([(2, 4), (3, 2), (5, 1), (7, 2), (7247, 1), (601135034269270369663, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_7, prime_oneHundredThirtyDX_7247, prime_oneHundredThirtyDX_601135034269270369663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008081 : Nat.totient 153694694933366915576477008081 = 153291926671560805383964311792 := by
  rw [← show ((([(383, 1), (103813, 1), (3865523890840349272739, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_383, prime_oneHundredThirtyDX_103813, prime_oneHundredThirtyDX_3865523890840349272739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008082 : Nat.totient 153694694933366915576477008082 = 75759797876294392780352664000 := by
  rw [← show ((([(2, 1), (71, 1), (14591, 1), (74179768800836573759281, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_71, prime_oneHundredThirtyDX_14591, prime_oneHundredThirtyDX_74179768800836573759281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008083 : Nat.totient 153694694933366915576477008083 = 101083163891550452706058371264 := by
  rw [← show ((([(3, 1), (89, 1), (443, 1), (1299403073472213758562043, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_89, prime_oneHundredThirtyDX_443, prime_oneHundredThirtyDX_1299403073472213758562043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008084 : Nat.totient 153694694933366915576477008084 = 76847347466379036818321961024 := by
  rw [← show ((([(2, 2), (252438177757, 1), (152210232520093753, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_252438177757, prime_oneHundredThirtyDX_152210232520093753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008085 : Nat.totient 153694694933366915576477008085 = 122952788229180610561308988800 := by
  rw [← show ((([(5, 1), (41627, 1), (8802841, 1), (83886273557254331, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_41627, prime_oneHundredThirtyDX_8802841, prime_oneHundredThirtyDX_83886273557254331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008086 : Nat.totient 153694694933366915576477008086 = 51231564977211961280514244328 := by
  rw [← show ((([(2, 1), (3, 1), (88787940239, 1), (288505200367772279, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_88787940239, prime_oneHundredThirtyDX_288505200367772279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008087 : Nat.totient 153694694933366915576477008087 = 119762044612555583893519324800 := by
  rw [← show ((([(7, 1), (11, 1), (3611317, 1), (5401373, 1), (102328915306291, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_7, prime_oneHundredThirtyDX_11, prime_oneHundredThirtyDX_3611317, prime_oneHundredThirtyDX_5401373, prime_oneHundredThirtyDX_102328915306291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008088 : Nat.totient 153694694933366915576477008088 = 76055106771150638635782436608 := by
  rw [← show ((([(2, 3), (97, 1), (198060173883204788114016763, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_97, prime_oneHundredThirtyDX_198060173883204788114016763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008089 : Nat.totient 153694694933366915576477008089 = 102177724343012196085451001600 := by
  rw [← show ((([(3, 2), (373, 1), (9551, 1), (16235579, 1), (295250682167513, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_373, prime_oneHundredThirtyDX_9551, prime_oneHundredThirtyDX_16235579, prime_oneHundredThirtyDX_295250682167513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008090 : Nat.totient 153694694933366915576477008090 = 54448654905649770700347740160 := by
  rw [← show ((([(2, 1), (5, 1), (17, 1), (19, 1), (163, 1), (1759, 1), (204859, 1), (810117218002061, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_17, prime_oneHundredThirtyDX_19, prime_oneHundredThirtyDX_163, prime_oneHundredThirtyDX_1759, prime_oneHundredThirtyDX_204859, prime_oneHundredThirtyDX_810117218002061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008091 : Nat.totient 153694694933366915576477008091 = 141789685972726190609952249312 := by
  rw [← show ((([(13, 1), (1723, 1), (6861676634375057617593509, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_13, prime_oneHundredThirtyDX_1723, prime_oneHundredThirtyDX_6861676634375057617593509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008092 : Nat.totient 153694694933366915576477008092 = 51230278870609216366961611200 := by
  rw [← show ((([(2, 2), (3, 1), (63901, 1), (105767, 1), (1895046148861394423, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_63901, prime_oneHundredThirtyDX_105767, prime_oneHundredThirtyDX_1895046148861394423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008093 : Nat.totient 153694694933366915576477008093 = 143426650627108044228313624640 := by
  rw [← show ((([(23, 2), (41, 1), (7086296967742492303770437, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_23, prime_oneHundredThirtyDX_41, prime_oneHundredThirtyDX_7086296967742492303770437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008094 : Nat.totient 153694694933366915576477008094 = 65796455508064181321765760000 := by
  rw [← show ((([(2, 1), (7, 1), (1171, 1), (4001, 1), (21473997583, 1), (109117019597, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_7, prime_oneHundredThirtyDX_1171, prime_oneHundredThirtyDX_4001, prime_oneHundredThirtyDX_21473997583, prime_oneHundredThirtyDX_109117019597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008095 : Nat.totient 153694694933366915576477008095 = 81970477649448839772075017120 := by
  rw [← show ((([(3, 1), (5, 1), (3114971, 1), (3289376689400252641763, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_3114971, prime_oneHundredThirtyDX_3289376689400252641763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008096 : Nat.totient 153694694933366915576477008096 = 76847347466683457788238504032 := by
  rw [← show ((([(2, 5), (4802959216667716111764906503, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_4802959216667716111764906503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008097 : Nat.totient 153694694933366915576477008097 = 151089700103987815312468923156 := by
  rw [← show ((([(59, 1), (2604994829379100264008084883, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_59, prime_oneHundredThirtyDX_2604994829379100264008084883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008098 : Nat.totient 153694694933366915576477008098 = 46548028744258602330679472640 := by
  rw [← show ((([(2, 1), (3, 3), (11, 1), (1783, 1), (6383555873, 1), (22733087583263, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_11, prime_oneHundredThirtyDX_1783, prime_oneHundredThirtyDX_6383555873, prime_oneHundredThirtyDX_22733087583263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008099 : Nat.totient 153694694933366915576477008099 = 151084531512084403621646305920 := by
  rw [← show ((([(61, 1), (1669, 1), (70936967429, 1), (21281394733559, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_61, prime_oneHundredThirtyDX_1669, prime_oneHundredThirtyDX_70936967429, prime_oneHundredThirtyDX_21281394733559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008100 : Nat.totient 153694694933366915576477008100 = 61029134338504819031827361280 := by
  rw [← show ((([(2, 2), (5, 2), (137, 1), (11218590871048679969085913, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_2, prime_oneHundredThirtyDX_5, prime_oneHundredThirtyDX_137, prime_oneHundredThirtyDX_11218590871048679969085913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyDX_153694694933366915576477008101 : Nat.totient 153694694933366915576477008101 = 87349546019026082833265405952 := by
  rw [← show ((([(3, 1), (7, 1), (233, 1), (1087, 1), (6829, 1), (15017, 1), (281782374136027, 1)] : List FactorBlock).map factorBlockValue).prod) = 153694694933366915576477008101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyDX_3, prime_oneHundredThirtyDX_7, prime_oneHundredThirtyDX_233, prime_oneHundredThirtyDX_1087, prime_oneHundredThirtyDX_6829, prime_oneHundredThirtyDX_15017, prime_oneHundredThirtyDX_281782374136027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredThirtyDX : certifiedKill 1 153694694933366915576477007999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredThirtyDX_153694694933366915576477008000, phi_oneHundredThirtyDX_153694694933366915576477008001, phi_oneHundredThirtyDX_153694694933366915576477008002,
    phi_oneHundredThirtyDX_153694694933366915576477008003, phi_oneHundredThirtyDX_153694694933366915576477008004, phi_oneHundredThirtyDX_153694694933366915576477008005,
    phi_oneHundredThirtyDX_153694694933366915576477008006, phi_oneHundredThirtyDX_153694694933366915576477008007, phi_oneHundredThirtyDX_153694694933366915576477008008,
    phi_oneHundredThirtyDX_153694694933366915576477008009, phi_oneHundredThirtyDX_153694694933366915576477008010, phi_oneHundredThirtyDX_153694694933366915576477008011,
    phi_oneHundredThirtyDX_153694694933366915576477008012, phi_oneHundredThirtyDX_153694694933366915576477008013, phi_oneHundredThirtyDX_153694694933366915576477008014,
    phi_oneHundredThirtyDX_153694694933366915576477008015, phi_oneHundredThirtyDX_153694694933366915576477008016, phi_oneHundredThirtyDX_153694694933366915576477008017,
    phi_oneHundredThirtyDX_153694694933366915576477008018, phi_oneHundredThirtyDX_153694694933366915576477008019, phi_oneHundredThirtyDX_153694694933366915576477008020,
    phi_oneHundredThirtyDX_153694694933366915576477008021, phi_oneHundredThirtyDX_153694694933366915576477008022, phi_oneHundredThirtyDX_153694694933366915576477008023,
    phi_oneHundredThirtyDX_153694694933366915576477008024, phi_oneHundredThirtyDX_153694694933366915576477008025, phi_oneHundredThirtyDX_153694694933366915576477008026,
    phi_oneHundredThirtyDX_153694694933366915576477008027, phi_oneHundredThirtyDX_153694694933366915576477008028, phi_oneHundredThirtyDX_153694694933366915576477008029,
    phi_oneHundredThirtyDX_153694694933366915576477008030, phi_oneHundredThirtyDX_153694694933366915576477008031, phi_oneHundredThirtyDX_153694694933366915576477008032,
    phi_oneHundredThirtyDX_153694694933366915576477008033, phi_oneHundredThirtyDX_153694694933366915576477008034, phi_oneHundredThirtyDX_153694694933366915576477008035,
    phi_oneHundredThirtyDX_153694694933366915576477008036, phi_oneHundredThirtyDX_153694694933366915576477008037, phi_oneHundredThirtyDX_153694694933366915576477008038,
    phi_oneHundredThirtyDX_153694694933366915576477008039, phi_oneHundredThirtyDX_153694694933366915576477008040, phi_oneHundredThirtyDX_153694694933366915576477008041,
    phi_oneHundredThirtyDX_153694694933366915576477008042, phi_oneHundredThirtyDX_153694694933366915576477008043, phi_oneHundredThirtyDX_153694694933366915576477008044,
    phi_oneHundredThirtyDX_153694694933366915576477008045, phi_oneHundredThirtyDX_153694694933366915576477008046, phi_oneHundredThirtyDX_153694694933366915576477008047,
    phi_oneHundredThirtyDX_153694694933366915576477008048, phi_oneHundredThirtyDX_153694694933366915576477008049, phi_oneHundredThirtyDX_153694694933366915576477008050,
    phi_oneHundredThirtyDX_153694694933366915576477008051, phi_oneHundredThirtyDX_153694694933366915576477008052, phi_oneHundredThirtyDX_153694694933366915576477008053,
    phi_oneHundredThirtyDX_153694694933366915576477008054, phi_oneHundredThirtyDX_153694694933366915576477008055, phi_oneHundredThirtyDX_153694694933366915576477008056,
    phi_oneHundredThirtyDX_153694694933366915576477008057, phi_oneHundredThirtyDX_153694694933366915576477008058, phi_oneHundredThirtyDX_153694694933366915576477008059,
    phi_oneHundredThirtyDX_153694694933366915576477008060, phi_oneHundredThirtyDX_153694694933366915576477008061, phi_oneHundredThirtyDX_153694694933366915576477008062,
    phi_oneHundredThirtyDX_153694694933366915576477008063, phi_oneHundredThirtyDX_153694694933366915576477008064, phi_oneHundredThirtyDX_153694694933366915576477008065,
    phi_oneHundredThirtyDX_153694694933366915576477008066, phi_oneHundredThirtyDX_153694694933366915576477008067, phi_oneHundredThirtyDX_153694694933366915576477008068,
    phi_oneHundredThirtyDX_153694694933366915576477008069, phi_oneHundredThirtyDX_153694694933366915576477008070, phi_oneHundredThirtyDX_153694694933366915576477008071,
    phi_oneHundredThirtyDX_153694694933366915576477008072, phi_oneHundredThirtyDX_153694694933366915576477008073, phi_oneHundredThirtyDX_153694694933366915576477008074,
    phi_oneHundredThirtyDX_153694694933366915576477008075, phi_oneHundredThirtyDX_153694694933366915576477008076, phi_oneHundredThirtyDX_153694694933366915576477008077,
    phi_oneHundredThirtyDX_153694694933366915576477008078, phi_oneHundredThirtyDX_153694694933366915576477008079, phi_oneHundredThirtyDX_153694694933366915576477008080,
    phi_oneHundredThirtyDX_153694694933366915576477008081, phi_oneHundredThirtyDX_153694694933366915576477008082, phi_oneHundredThirtyDX_153694694933366915576477008083,
    phi_oneHundredThirtyDX_153694694933366915576477008084, phi_oneHundredThirtyDX_153694694933366915576477008085, phi_oneHundredThirtyDX_153694694933366915576477008086,
    phi_oneHundredThirtyDX_153694694933366915576477008087, phi_oneHundredThirtyDX_153694694933366915576477008088, phi_oneHundredThirtyDX_153694694933366915576477008089,
    phi_oneHundredThirtyDX_153694694933366915576477008090, phi_oneHundredThirtyDX_153694694933366915576477008091, phi_oneHundredThirtyDX_153694694933366915576477008092,
    phi_oneHundredThirtyDX_153694694933366915576477008093, phi_oneHundredThirtyDX_153694694933366915576477008094, phi_oneHundredThirtyDX_153694694933366915576477008095,
    phi_oneHundredThirtyDX_153694694933366915576477008096, phi_oneHundredThirtyDX_153694694933366915576477008097, phi_oneHundredThirtyDX_153694694933366915576477008098,
    phi_oneHundredThirtyDX_153694694933366915576477008099, phi_oneHundredThirtyDX_153694694933366915576477008100, phi_oneHundredThirtyDX_153694694933366915576477008101
    ]

end TotientTailPeriodKiller
end Erdos249257
