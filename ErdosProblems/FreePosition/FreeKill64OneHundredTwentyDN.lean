import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredTwentyDNFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredTwentyDNFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredTwentyDNFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredTwentyDNFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredTwentyDNFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredTwentyDNFastPow a n * oneHundredTwentyDNFastPow a n * a else oneHundredTwentyDNFastPow a n * oneHundredTwentyDNFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredTwentyDN_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredTwentyDN_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredTwentyDN_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredTwentyDN_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredTwentyDN_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredTwentyDN_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredTwentyDN_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredTwentyDN_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredTwentyDN_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredTwentyDN_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredTwentyDN_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredTwentyDN_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredTwentyDN_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredTwentyDN_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredTwentyDN_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredTwentyDN_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredTwentyDN_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredTwentyDN_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredTwentyDN_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredTwentyDN_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredTwentyDN_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredTwentyDN_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredTwentyDN_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredTwentyDN_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredTwentyDN_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredTwentyDN_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredTwentyDN_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredTwentyDN_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredTwentyDN_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredTwentyDN_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredTwentyDN_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredTwentyDN_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredTwentyDN_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredTwentyDN_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredTwentyDN_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredTwentyDN_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredTwentyDN_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredTwentyDN_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredTwentyDN_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredTwentyDN_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredTwentyDN_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredTwentyDN_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredTwentyDN_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredTwentyDN_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredTwentyDN_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredTwentyDN_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredTwentyDN_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredTwentyDN_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredTwentyDN_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredTwentyDN_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredTwentyDN_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredTwentyDN_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredTwentyDN_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredTwentyDN_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredTwentyDN_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredTwentyDN_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredTwentyDN_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredTwentyDN_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredTwentyDN_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredTwentyDN_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredTwentyDN_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredTwentyDN_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredTwentyDN_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredTwentyDN_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredTwentyDN_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredTwentyDN_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredTwentyDN_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredTwentyDN_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredTwentyDN_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredTwentyDN_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredTwentyDN_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredTwentyDN_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredTwentyDN_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredTwentyDN_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredTwentyDN_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredTwentyDN_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredTwentyDN_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredTwentyDN_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredTwentyDN_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredTwentyDN_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredTwentyDN_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredTwentyDN_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredTwentyDN_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredTwentyDN_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredTwentyDN_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredTwentyDN_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredTwentyDN_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredTwentyDN_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredTwentyDN_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredTwentyDN_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredTwentyDN_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredTwentyDN_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredTwentyDN_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredTwentyDN_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredTwentyDN_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredTwentyDN_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredTwentyDN_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredTwentyDN_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredTwentyDN_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredTwentyDN_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredTwentyDN_863 : Nat.Prime 863 := by norm_num

private theorem prime_oneHundredTwentyDN_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredTwentyDN_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredTwentyDN_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredTwentyDN_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredTwentyDN_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_oneHundredTwentyDN_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_oneHundredTwentyDN_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredTwentyDN_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_oneHundredTwentyDN_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_oneHundredTwentyDN_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_oneHundredTwentyDN_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredTwentyDN_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_oneHundredTwentyDN_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredTwentyDN_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_oneHundredTwentyDN_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_oneHundredTwentyDN_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_oneHundredTwentyDN_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_oneHundredTwentyDN_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredTwentyDN_1213 : Nat.Prime 1213 := by norm_num

private theorem prime_oneHundredTwentyDN_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredTwentyDN_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_oneHundredTwentyDN_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_oneHundredTwentyDN_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_oneHundredTwentyDN_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_oneHundredTwentyDN_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredTwentyDN_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_oneHundredTwentyDN_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_oneHundredTwentyDN_1471 : Nat.Prime 1471 := by norm_num

private theorem prime_oneHundredTwentyDN_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_oneHundredTwentyDN_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredTwentyDN_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_oneHundredTwentyDN_1663 : Nat.Prime 1663 := by norm_num

private theorem prime_oneHundredTwentyDN_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_oneHundredTwentyDN_1697 : Nat.Prime 1697 := by norm_num

private theorem prime_oneHundredTwentyDN_1699 : Nat.Prime 1699 := by norm_num

private theorem prime_oneHundredTwentyDN_1723 : Nat.Prime 1723 := by norm_num

private theorem prime_oneHundredTwentyDN_1777 : Nat.Prime 1777 := by norm_num

private theorem prime_oneHundredTwentyDN_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_oneHundredTwentyDN_1787 : Nat.Prime 1787 := by norm_num

private theorem prime_oneHundredTwentyDN_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredTwentyDN_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_oneHundredTwentyDN_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_oneHundredTwentyDN_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_oneHundredTwentyDN_1931 : Nat.Prime 1931 := by norm_num

private theorem prime_oneHundredTwentyDN_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredTwentyDN_2243 : Nat.Prime 2243 := by norm_num

private theorem prime_oneHundredTwentyDN_2309 : Nat.Prime 2309 := by norm_num

private theorem prime_oneHundredTwentyDN_2333 : Nat.Prime 2333 := by norm_num

private theorem prime_oneHundredTwentyDN_2347 : Nat.Prime 2347 := by norm_num

private theorem prime_oneHundredTwentyDN_2351 : Nat.Prime 2351 := by norm_num

private theorem prime_oneHundredTwentyDN_2441 : Nat.Prime 2441 := by norm_num

private theorem prime_oneHundredTwentyDN_2591 : Nat.Prime 2591 := by norm_num

private theorem prime_oneHundredTwentyDN_2609 : Nat.Prime 2609 := by norm_num

private theorem prime_oneHundredTwentyDN_2647 : Nat.Prime 2647 := by norm_num

private theorem prime_oneHundredTwentyDN_2729 : Nat.Prime 2729 := by norm_num

private theorem prime_oneHundredTwentyDN_2767 : Nat.Prime 2767 := by norm_num

private theorem prime_oneHundredTwentyDN_2879 : Nat.Prime 2879 := by norm_num

private theorem prime_oneHundredTwentyDN_2909 : Nat.Prime 2909 := by norm_num

private theorem prime_oneHundredTwentyDN_2971 : Nat.Prime 2971 := by norm_num

private theorem prime_oneHundredTwentyDN_3001 : Nat.Prime 3001 := by norm_num

private theorem prime_oneHundredTwentyDN_3011 : Nat.Prime 3011 := by norm_num

private theorem prime_oneHundredTwentyDN_3067 : Nat.Prime 3067 := by norm_num

private theorem prime_oneHundredTwentyDN_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_oneHundredTwentyDN_3253 : Nat.Prime 3253 := by norm_num

private theorem prime_oneHundredTwentyDN_3359 : Nat.Prime 3359 := by norm_num

private theorem prime_oneHundredTwentyDN_3449 : Nat.Prime 3449 := by norm_num

private theorem prime_oneHundredTwentyDN_3461 : Nat.Prime 3461 := by norm_num

private theorem prime_oneHundredTwentyDN_3581 : Nat.Prime 3581 := by norm_num

private theorem prime_oneHundredTwentyDN_3637 : Nat.Prime 3637 := by norm_num

private theorem prime_oneHundredTwentyDN_3701 : Nat.Prime 3701 := by norm_num

private theorem prime_oneHundredTwentyDN_3919 : Nat.Prime 3919 := by norm_num

private theorem prime_oneHundredTwentyDN_4217 : Nat.Prime 4217 := by norm_num

private theorem prime_oneHundredTwentyDN_4253 : Nat.Prime 4253 := by norm_num

private theorem prime_oneHundredTwentyDN_4273 : Nat.Prime 4273 := by norm_num

private theorem prime_oneHundredTwentyDN_4547 : Nat.Prime 4547 := by norm_num

private theorem prime_oneHundredTwentyDN_4621 : Nat.Prime 4621 := by norm_num

private theorem prime_oneHundredTwentyDN_4937 : Nat.Prime 4937 := by norm_num

private theorem prime_oneHundredTwentyDN_5077 : Nat.Prime 5077 := by norm_num

private theorem prime_oneHundredTwentyDN_5179 : Nat.Prime 5179 := by norm_num

private theorem prime_oneHundredTwentyDN_5273 : Nat.Prime 5273 := by norm_num

private theorem prime_oneHundredTwentyDN_5419 : Nat.Prime 5419 := by norm_num

private theorem prime_oneHundredTwentyDN_5501 : Nat.Prime 5501 := by norm_num

private theorem prime_oneHundredTwentyDN_5651 : Nat.Prime 5651 := by norm_num

private theorem prime_oneHundredTwentyDN_5701 : Nat.Prime 5701 := by norm_num

private theorem prime_oneHundredTwentyDN_5821 : Nat.Prime 5821 := by norm_num

private theorem prime_oneHundredTwentyDN_5879 : Nat.Prime 5879 := by norm_num

private theorem prime_oneHundredTwentyDN_6047 : Nat.Prime 6047 := by norm_num

private theorem prime_oneHundredTwentyDN_6277 : Nat.Prime 6277 := by norm_num

private theorem prime_oneHundredTwentyDN_6323 : Nat.Prime 6323 := by norm_num

private theorem prime_oneHundredTwentyDN_6337 : Nat.Prime 6337 := by norm_num

private theorem prime_oneHundredTwentyDN_6451 : Nat.Prime 6451 := by norm_num

private theorem prime_oneHundredTwentyDN_6689 : Nat.Prime 6689 := by norm_num

private theorem prime_oneHundredTwentyDN_6863 : Nat.Prime 6863 := by norm_num

private theorem prime_oneHundredTwentyDN_7351 : Nat.Prime 7351 := by norm_num

private theorem prime_oneHundredTwentyDN_7459 : Nat.Prime 7459 := by norm_num

private theorem prime_oneHundredTwentyDN_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_oneHundredTwentyDN_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredTwentyDN_8387 : Nat.Prime 8387 := by norm_num

private theorem prime_oneHundredTwentyDN_8431 : Nat.Prime 8431 := by norm_num

private theorem prime_oneHundredTwentyDN_8563 : Nat.Prime 8563 := by norm_num

private theorem prime_oneHundredTwentyDN_8753 : Nat.Prime 8753 := by norm_num

private theorem prime_oneHundredTwentyDN_8761 : Nat.Prime 8761 := by norm_num

private theorem prime_oneHundredTwentyDN_8783 : Nat.Prime 8783 := by norm_num

private theorem prime_oneHundredTwentyDN_8849 : Nat.Prime 8849 := by norm_num

private theorem prime_oneHundredTwentyDN_8951 : Nat.Prime 8951 := by norm_num

private theorem prime_oneHundredTwentyDN_9043 : Nat.Prime 9043 := by norm_num

private theorem prime_oneHundredTwentyDN_9103 : Nat.Prime 9103 := by norm_num

private theorem prime_oneHundredTwentyDN_9203 : Nat.Prime 9203 := by norm_num

private theorem prime_oneHundredTwentyDN_9221 : Nat.Prime 9221 := by norm_num

private theorem prime_oneHundredTwentyDN_9739 : Nat.Prime 9739 := by norm_num

private theorem prime_oneHundredTwentyDN_10259 : Nat.Prime 10259 := by norm_num

private theorem prime_oneHundredTwentyDN_10789 : Nat.Prime 10789 := by norm_num

private theorem prime_oneHundredTwentyDN_11161 : Nat.Prime 11161 := by norm_num

private theorem prime_oneHundredTwentyDN_11353 : Nat.Prime 11353 := by norm_num

private theorem prime_oneHundredTwentyDN_11437 : Nat.Prime 11437 := by norm_num

private theorem prime_oneHundredTwentyDN_11593 : Nat.Prime 11593 := by norm_num

private theorem prime_oneHundredTwentyDN_11969 : Nat.Prime 11969 := by norm_num

private theorem prime_oneHundredTwentyDN_12539 : Nat.Prime 12539 := by norm_num

private theorem prime_oneHundredTwentyDN_12823 : Nat.Prime 12823 := by norm_num

private theorem prime_oneHundredTwentyDN_13151 : Nat.Prime 13151 := by norm_num

private theorem prime_oneHundredTwentyDN_13327 : Nat.Prime 13327 := by norm_num

private theorem prime_oneHundredTwentyDN_13463 : Nat.Prime 13463 := by norm_num

private theorem prime_oneHundredTwentyDN_14389 : Nat.Prime 14389 := by norm_num

private theorem prime_oneHundredTwentyDN_14437 : Nat.Prime 14437 := by norm_num

private theorem prime_oneHundredTwentyDN_14753 : Nat.Prime 14753 := by norm_num

private theorem prime_oneHundredTwentyDN_14891 : Nat.Prime 14891 := by norm_num

private theorem prime_oneHundredTwentyDN_15269 : Nat.Prime 15269 := by norm_num

private theorem prime_oneHundredTwentyDN_15647 : Nat.Prime 15647 := by norm_num

private theorem prime_oneHundredTwentyDN_15817 : Nat.Prime 15817 := by norm_num

private theorem prime_oneHundredTwentyDN_15971 : Nat.Prime 15971 := by norm_num

private theorem prime_oneHundredTwentyDN_16631 : Nat.Prime 16631 := by norm_num

private theorem prime_oneHundredTwentyDN_16651 : Nat.Prime 16651 := by norm_num

private theorem prime_oneHundredTwentyDN_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredTwentyDN_17351 : Nat.Prime 17351 := by norm_num

private theorem prime_oneHundredTwentyDN_17509 : Nat.Prime 17509 := by norm_num

private theorem prime_oneHundredTwentyDN_17681 : Nat.Prime 17681 := by norm_num

private theorem prime_oneHundredTwentyDN_18061 : Nat.Prime 18061 := by norm_num

private theorem prime_oneHundredTwentyDN_19471 : Nat.Prime 19471 := by norm_num

private theorem prime_oneHundredTwentyDN_20357 : Nat.Prime 20357 := by norm_num

private theorem prime_oneHundredTwentyDN_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredTwentyDN_20903 : Nat.Prime 20903 := by norm_num

private theorem prime_oneHundredTwentyDN_21143 : Nat.Prime 21143 := by norm_num

private theorem prime_oneHundredTwentyDN_21617 : Nat.Prime 21617 := by norm_num

private theorem prime_oneHundredTwentyDN_22003 : Nat.Prime 22003 := by norm_num

private theorem prime_oneHundredTwentyDN_22453 : Nat.Prime 22453 := by norm_num

private theorem prime_oneHundredTwentyDN_23057 : Nat.Prime 23057 := by norm_num

private theorem prime_oneHundredTwentyDN_24019 : Nat.Prime 24019 := by norm_num

private theorem prime_oneHundredTwentyDN_24133 : Nat.Prime 24133 := by norm_num

private theorem prime_oneHundredTwentyDN_24841 : Nat.Prime 24841 := by norm_num

private theorem prime_oneHundredTwentyDN_25117 : Nat.Prime 25117 := by norm_num

private theorem prime_oneHundredTwentyDN_25189 : Nat.Prime 25189 := by norm_num

private theorem prime_oneHundredTwentyDN_25471 : Nat.Prime 25471 := by norm_num

private theorem prime_oneHundredTwentyDN_25541 : Nat.Prime 25541 := by norm_num

private theorem prime_oneHundredTwentyDN_25933 : Nat.Prime 25933 := by norm_num

private theorem prime_oneHundredTwentyDN_27431 : Nat.Prime 27431 := by norm_num

private theorem prime_oneHundredTwentyDN_28097 : Nat.Prime 28097 := by norm_num

private theorem prime_oneHundredTwentyDN_28793 : Nat.Prime 28793 := by norm_num

private theorem prime_oneHundredTwentyDN_31177 : Nat.Prime 31177 := by norm_num

private theorem prime_oneHundredTwentyDN_33347 : Nat.Prime 33347 := by norm_num

private theorem prime_oneHundredTwentyDN_33589 : Nat.Prime 33589 := by norm_num

private theorem prime_oneHundredTwentyDN_33617 : Nat.Prime 33617 := by norm_num

private theorem prime_oneHundredTwentyDN_33721 : Nat.Prime 33721 := by norm_num

private theorem prime_oneHundredTwentyDN_34057 : Nat.Prime 34057 := by norm_num

private theorem prime_oneHundredTwentyDN_35023 : Nat.Prime 35023 := by norm_num

private theorem prime_oneHundredTwentyDN_35267 : Nat.Prime 35267 := by norm_num

private theorem prime_oneHundredTwentyDN_36083 : Nat.Prime 36083 := by norm_num

private theorem prime_oneHundredTwentyDN_41777 : Nat.Prime 41777 := by norm_num

private theorem prime_oneHundredTwentyDN_43063 : Nat.Prime 43063 := by norm_num

private theorem prime_oneHundredTwentyDN_45389 : Nat.Prime 45389 := by norm_num

private theorem prime_oneHundredTwentyDN_47713 : Nat.Prime 47713 := by norm_num

private theorem prime_oneHundredTwentyDN_47981 : Nat.Prime 47981 := by norm_num

private theorem prime_oneHundredTwentyDN_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredTwentyDN_49433 : Nat.Prime 49433 := by norm_num

private theorem prime_oneHundredTwentyDN_49823 : Nat.Prime 49823 := by norm_num

private theorem prime_oneHundredTwentyDN_50461 : Nat.Prime 50461 := by norm_num

private theorem prime_oneHundredTwentyDN_52561 : Nat.Prime 52561 := by norm_num

private theorem prime_oneHundredTwentyDN_53279 : Nat.Prime 53279 := by norm_num

private theorem prime_oneHundredTwentyDN_54403 : Nat.Prime 54403 := by norm_num

private theorem prime_oneHundredTwentyDN_54829 : Nat.Prime 54829 := by norm_num

private theorem prime_oneHundredTwentyDN_54973 : Nat.Prime 54973 := by norm_num

private theorem prime_oneHundredTwentyDN_56489 : Nat.Prime 56489 := by norm_num

private theorem prime_oneHundredTwentyDN_59183 : Nat.Prime 59183 := by norm_num

private theorem prime_oneHundredTwentyDN_60607 : Nat.Prime 60607 := by norm_num

private theorem prime_oneHundredTwentyDN_67231 : Nat.Prime 67231 := by norm_num

private theorem prime_oneHundredTwentyDN_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredTwentyDN_70249 : Nat.Prime 70249 := by norm_num

private theorem prime_oneHundredTwentyDN_70501 : Nat.Prime 70501 := by norm_num

private theorem prime_oneHundredTwentyDN_71663 : Nat.Prime 71663 := by norm_num

private theorem prime_oneHundredTwentyDN_71999 : Nat.Prime 71999 := by norm_num

private theorem prime_oneHundredTwentyDN_72959 : Nat.Prime 72959 := by norm_num

private theorem prime_oneHundredTwentyDN_73079 : Nat.Prime 73079 := by norm_num

private theorem prime_oneHundredTwentyDN_81769 : Nat.Prime 81769 := by norm_num

private theorem prime_oneHundredTwentyDN_85243 : Nat.Prime 85243 := by norm_num

private theorem prime_oneHundredTwentyDN_87643 : Nat.Prime 87643 := by norm_num

private theorem prime_oneHundredTwentyDN_88873 : Nat.Prime 88873 := by norm_num

private theorem prime_oneHundredTwentyDN_90173 : Nat.Prime 90173 := by norm_num

private theorem prime_oneHundredTwentyDN_91541 : Nat.Prime 91541 := by norm_num

private theorem prime_oneHundredTwentyDN_96697 : Nat.Prime 96697 := by norm_num

private theorem prime_oneHundredTwentyDN_103573 : Nat.Prime 103573 := by norm_num

private theorem prime_oneHundredTwentyDN_106433 : Nat.Prime 106433 := by norm_num

private theorem prime_oneHundredTwentyDN_107071 : Nat.Prime 107071 := by norm_num

private theorem prime_oneHundredTwentyDN_112997 : Nat.Prime 112997 := by norm_num

private theorem prime_oneHundredTwentyDN_113621 : Nat.Prime 113621 := by norm_num

private theorem prime_oneHundredTwentyDN_114269 : Nat.Prime 114269 := by norm_num

private theorem prime_oneHundredTwentyDN_115183 : Nat.Prime 115183 := by norm_num

private theorem prime_oneHundredTwentyDN_121661 : Nat.Prime 121661 := by norm_num

private theorem prime_oneHundredTwentyDN_125183 : Nat.Prime 125183 := by norm_num

private theorem prime_oneHundredTwentyDN_125287 : Nat.Prime 125287 := by norm_num

private theorem prime_oneHundredTwentyDN_125627 : Nat.Prime 125627 := by norm_num

private theorem prime_oneHundredTwentyDN_130073 : Nat.Prime 130073 := by norm_num

private theorem prime_oneHundredTwentyDN_132257 : Nat.Prime 132257 := by norm_num

private theorem prime_oneHundredTwentyDN_132763 : Nat.Prime 132763 := by norm_num

private theorem prime_oneHundredTwentyDN_133723 : Nat.Prime 133723 := by norm_num

private theorem prime_oneHundredTwentyDN_144511 : Nat.Prime 144511 := by norm_num

private theorem prime_oneHundredTwentyDN_147647 : Nat.Prime 147647 := by norm_num

private theorem prime_oneHundredTwentyDN_152597 : Nat.Prime 152597 := by norm_num

private theorem prime_oneHundredTwentyDN_155291 : Nat.Prime 155291 := by norm_num

private theorem prime_oneHundredTwentyDN_160813 : Nat.Prime 160813 := by norm_num

private theorem prime_oneHundredTwentyDN_166853 : Nat.Prime 166853 := by norm_num

private theorem prime_oneHundredTwentyDN_170603 : Nat.Prime 170603 := by norm_num

private theorem prime_oneHundredTwentyDN_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredTwentyDN_173039 : Nat.Prime 173039 := by norm_num

private theorem prime_oneHundredTwentyDN_181943 : Nat.Prime 181943 := by norm_num

private theorem prime_oneHundredTwentyDN_182123 : Nat.Prime 182123 := by norm_num

private theorem prime_oneHundredTwentyDN_183263 : Nat.Prime 183263 := by norm_num

private theorem prime_oneHundredTwentyDN_185153 : Nat.Prime 185153 := by norm_num

private theorem prime_oneHundredTwentyDN_189391 : Nat.Prime 189391 := by norm_num

private theorem prime_oneHundredTwentyDN_200131 : Nat.Prime 200131 := by norm_num

private theorem prime_oneHundredTwentyDN_204557 : Nat.Prime 204557 := by norm_num

private theorem prime_oneHundredTwentyDN_213079 : Nat.Prime 213079 := by norm_num

private theorem prime_oneHundredTwentyDN_230551 : Nat.Prime 230551 := by norm_num

private theorem prime_oneHundredTwentyDN_235397 : Nat.Prime 235397 := by norm_num

private theorem prime_oneHundredTwentyDN_245299 : Nat.Prime 245299 := by norm_num

private theorem prime_oneHundredTwentyDN_254731 : Nat.Prime 254731 := by norm_num

private theorem prime_oneHundredTwentyDN_256643 : Nat.Prime 256643 := by norm_num

private theorem prime_oneHundredTwentyDN_263399 : Nat.Prime 263399 := by norm_num

private theorem prime_oneHundredTwentyDN_278717 : Nat.Prime 278717 := by norm_num

private theorem prime_oneHundredTwentyDN_279029 : Nat.Prime 279029 := by norm_num

private theorem prime_oneHundredTwentyDN_280607 : Nat.Prime 280607 := by norm_num

private theorem prime_oneHundredTwentyDN_317371 : Nat.Prime 317371 := by norm_num

private theorem prime_oneHundredTwentyDN_340633 : Nat.Prime 340633 := by norm_num

private theorem prime_oneHundredTwentyDN_341461 : Nat.Prime 341461 := by norm_num

private theorem prime_oneHundredTwentyDN_342179 : Nat.Prime 342179 := by norm_num

private theorem prime_oneHundredTwentyDN_362027 : Nat.Prime 362027 := by norm_num

private theorem prime_oneHundredTwentyDN_426707 : Nat.Prime 426707 := by norm_num

private theorem prime_oneHundredTwentyDN_453227 : Nat.Prime 453227 := by norm_num

private theorem prime_oneHundredTwentyDN_460711 : Nat.Prime 460711 := by norm_num

private theorem prime_oneHundredTwentyDN_519119 : Nat.Prime 519119 := by norm_num

private theorem prime_oneHundredTwentyDN_559939 : Nat.Prime 559939 := by norm_num

private theorem prime_oneHundredTwentyDN_589861 : Nat.Prime 589861 := by norm_num

private theorem prime_oneHundredTwentyDN_601543 : Nat.Prime 601543 := by norm_num

private theorem prime_oneHundredTwentyDN_602411 : Nat.Prime 602411 := by norm_num

private theorem prime_oneHundredTwentyDN_607213 : Nat.Prime 607213 := by norm_num

private theorem prime_oneHundredTwentyDN_656749 : Nat.Prime 656749 := by norm_num

private theorem prime_oneHundredTwentyDN_676337 : Nat.Prime 676337 := by norm_num

private theorem prime_oneHundredTwentyDN_702239 : Nat.Prime 702239 := by norm_num

private theorem prime_oneHundredTwentyDN_723133 : Nat.Prime 723133 := by norm_num

private theorem prime_oneHundredTwentyDN_822011 : Nat.Prime 822011 := by norm_num

private theorem prime_oneHundredTwentyDN_822131 : Nat.Prime 822131 := by norm_num

private theorem prime_oneHundredTwentyDN_870169 : Nat.Prime 870169 := by norm_num

private theorem prime_oneHundredTwentyDN_894689 : Nat.Prime 894689 := by norm_num

private theorem prime_oneHundredTwentyDN_950531 : Nat.Prime 950531 := by norm_num

private theorem prime_oneHundredTwentyDN_958183 : Nat.Prime 958183 := by norm_num

private theorem prime_oneHundredTwentyDN_1001989 : Nat.Prime 1001989 := by norm_num

private theorem prime_oneHundredTwentyDN_1018559 : Nat.Prime 1018559 := by norm_num

private theorem prime_oneHundredTwentyDN_1030817 : Nat.Prime 1030817 := by norm_num

private theorem prime_oneHundredTwentyDN_1116419 : Nat.Prime 1116419 := by norm_num

private theorem prime_oneHundredTwentyDN_1126649 : Nat.Prime 1126649 := by norm_num

private theorem prime_oneHundredTwentyDN_1150063 : Nat.Prime 1150063 := by norm_num

private theorem prime_oneHundredTwentyDN_1229519 : Nat.Prime 1229519 := by norm_num

private theorem prime_oneHundredTwentyDN_1243169 : Nat.Prime 1243169 := by norm_num

private theorem prime_oneHundredTwentyDN_1281083 : Nat.Prime 1281083 := by norm_num

private theorem prime_oneHundredTwentyDN_1431847 : Nat.Prime 1431847 := by norm_num

private theorem prime_oneHundredTwentyDN_1632467 : Nat.Prime 1632467 := by norm_num

private theorem prime_oneHundredTwentyDN_1901651 : Nat.Prime 1901651 := by norm_num

private theorem prime_oneHundredTwentyDN_2126771 : Nat.Prime 2126771 := by norm_num

private theorem prime_oneHundredTwentyDN_2160149 : Nat.Prime 2160149 := by norm_num

private theorem prime_oneHundredTwentyDN_2174941 : Nat.Prime 2174941 := by norm_num

private theorem prime_oneHundredTwentyDN_2227417 : Nat.Prime 2227417 := by norm_num

private theorem prime_oneHundredTwentyDN_2276699 : Nat.Prime 2276699 := by norm_num

private theorem prime_oneHundredTwentyDN_2310083 : Nat.Prime 2310083 := by norm_num

private theorem prime_oneHundredTwentyDN_2421541 : Nat.Prime 2421541 := by norm_num

private theorem prime_oneHundredTwentyDN_2437507 : Nat.Prime 2437507 := by norm_num

private theorem prime_oneHundredTwentyDN_2500999 : Nat.Prime 2500999 := by norm_num

private theorem prime_oneHundredTwentyDN_2548751 : Nat.Prime 2548751 := by norm_num

private theorem prime_oneHundredTwentyDN_2755243 : Nat.Prime 2755243 := by norm_num

private theorem prime_oneHundredTwentyDN_2841961 : Nat.Prime 2841961 := by norm_num

private theorem prime_oneHundredTwentyDN_3287311 : Nat.Prime 3287311 := by norm_num

private theorem prime_oneHundredTwentyDN_3355867 : Nat.Prime 3355867 := by norm_num

private theorem prime_oneHundredTwentyDN_3594403 : Nat.Prime 3594403 := by norm_num

private theorem prime_oneHundredTwentyDN_3599009 : Nat.Prime 3599009 := by norm_num

private theorem prime_oneHundredTwentyDN_3608377 : Nat.Prime 3608377 := by norm_num

private theorem prime_oneHundredTwentyDN_4438201 : Nat.Prime 4438201 := by norm_num

private theorem prime_oneHundredTwentyDN_4440187 : Nat.Prime 4440187 := by norm_num

private theorem prime_oneHundredTwentyDN_4517543 : Nat.Prime 4517543 := by norm_num

private theorem prime_oneHundredTwentyDN_4671071 : Nat.Prime 4671071 := by norm_num

private theorem prime_oneHundredTwentyDN_4943441 : Nat.Prime 4943441 := by norm_num

private theorem prime_oneHundredTwentyDN_5321087 : Nat.Prime 5321087 := by norm_num

private theorem prime_oneHundredTwentyDN_5627161 : Nat.Prime 5627161 := by norm_num

private theorem prime_oneHundredTwentyDN_5653909 : Nat.Prime 5653909 := by norm_num

private theorem prime_oneHundredTwentyDN_6069853 : Nat.Prime 6069853 := by norm_num

private theorem prime_oneHundredTwentyDN_6189961 : Nat.Prime 6189961 := by norm_num

private theorem prime_oneHundredTwentyDN_6336347 : Nat.Prime 6336347 := by norm_num

private theorem prime_oneHundredTwentyDN_7370491 : Nat.Prime 7370491 := by norm_num

private theorem prime_oneHundredTwentyDN_7467511 : Nat.Prime 7467511 := by norm_num

private theorem prime_oneHundredTwentyDN_8095547 : Nat.Prime 8095547 := by norm_num

private theorem prime_oneHundredTwentyDN_8105401 : Nat.Prime 8105401 := by norm_num

private theorem prime_oneHundredTwentyDN_8116753 : Nat.Prime 8116753 := by norm_num

private theorem prime_oneHundredTwentyDN_9204133 : Nat.Prime 9204133 := by norm_num

private theorem prime_oneHundredTwentyDN_9529907 : Nat.Prime 9529907 := by norm_num

private theorem prime_oneHundredTwentyDN_9554807 : Nat.Prime 9554807 := by norm_num

private theorem prime_oneHundredTwentyDN_10031591 : Nat.Prime 10031591 := by norm_num

private theorem prime_oneHundredTwentyDN_10163389 : Nat.Prime 10163389 := by norm_num

private theorem prime_oneHundredTwentyDN_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredTwentyDN_11292583 : Nat.Prime 11292583 := by norm_num

private theorem prime_oneHundredTwentyDN_11333351 : Nat.Prime 11333351 := by norm_num

private theorem prime_oneHundredTwentyDN_11400793 : Nat.Prime 11400793 := by norm_num

private theorem prime_oneHundredTwentyDN_12300311 : Nat.Prime 12300311 := by norm_num

private theorem prime_oneHundredTwentyDN_13023389 : Nat.Prime 13023389 := by norm_num

private theorem prime_oneHundredTwentyDN_13151923 : Nat.Prime 13151923 := by norm_num

private theorem prime_oneHundredTwentyDN_13311367 : Nat.Prime 13311367 := by norm_num

private theorem prime_oneHundredTwentyDN_13617913 : Nat.Prime 13617913 := by norm_num

private theorem prime_oneHundredTwentyDN_14198059 : Nat.Prime 14198059 := by norm_num

private theorem prime_oneHundredTwentyDN_14201963 : Nat.Prime 14201963 := by norm_num

private theorem prime_oneHundredTwentyDN_14492537 : Nat.Prime 14492537 := by norm_num

private theorem prime_oneHundredTwentyDN_14986001 : Nat.Prime 14986001 := by norm_num

private theorem prime_oneHundredTwentyDN_15373961 : Nat.Prime 15373961 := by norm_num

private theorem prime_oneHundredTwentyDN_16666033 : Nat.Prime 16666033 := by norm_num

private theorem prime_oneHundredTwentyDN_17285633 : Nat.Prime 17285633 := by norm_num

private theorem prime_oneHundredTwentyDN_17435513 : Nat.Prime 17435513 := by norm_num

private theorem prime_oneHundredTwentyDN_17468093 : Nat.Prime 17468093 := by norm_num

private theorem prime_oneHundredTwentyDN_17957579 : Nat.Prime 17957579 := by norm_num

private theorem prime_oneHundredTwentyDN_18151967 : Nat.Prime 18151967 := by norm_num

private theorem prime_oneHundredTwentyDN_20291147 : Nat.Prime 20291147 := by norm_num

private theorem prime_oneHundredTwentyDN_20313841 : Nat.Prime 20313841 := by norm_num

private theorem prime_oneHundredTwentyDN_21610411 : Nat.Prime 21610411 := by norm_num

private theorem prime_oneHundredTwentyDN_25512737 : Nat.Prime 25512737 := by norm_num

private theorem prime_oneHundredTwentyDN_30189371 : Nat.Prime 30189371 := by
  apply lucas_primality 30189371 (2 : ZMod 30189371)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1667, 1), (1811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1667, 1), (1811, 1)] : List FactorBlock).map factorBlockValue).prod) = 30189371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_1667
      · exact prime_oneHundredTwentyDN_1811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30189371) ^ 15094685 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 30189371) ^ 6037874 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 30189371) ^ 18110 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 30189371) ^ 16670 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_30747923 : Nat.Prime 30747923 := by
  apply lucas_primality 30747923 (2 : ZMod 30747923)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (15373961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (15373961, 1)] : List FactorBlock).map factorBlockValue).prod) = 30747923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_15373961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 30747923) ^ 15373961 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 30747923) ^ 2 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_32746729 : Nat.Prime 32746729 := by
  apply lucas_primality 32746729 (17 : ZMod 32746729)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (19, 1), (10259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (19, 1), (10259, 1)] : List FactorBlock).map factorBlockValue).prod) = 32746729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_10259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 32746729) ^ 16373364 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 32746729) ^ 10915576 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 32746729) ^ 4678104 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 32746729) ^ 1723512 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 32746729) ^ 3192 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_33364553 : Nat.Prime 33364553 := by
  apply lucas_primality 33364553 (3 : ZMod 33364553)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (541, 1), (593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (541, 1), (593, 1)] : List FactorBlock).map factorBlockValue).prod) = 33364553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_541
      · exact prime_oneHundredTwentyDN_593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 33364553) ^ 16682276 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 33364553) ^ 2566504 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 33364553) ^ 61672 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 33364553) ^ 56264 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_34871027 : Nat.Prime 34871027 := by
  apply lucas_primality 34871027 (2 : ZMod 34871027)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17435513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17435513, 1)] : List FactorBlock).map factorBlockValue).prod) = 34871027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_17435513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 34871027) ^ 17435513 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 34871027) ^ 2 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_34877723 : Nat.Prime 34877723 := by
  apply lucas_primality 34877723 (2 : ZMod 34877723)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (821, 1), (1931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (821, 1), (1931, 1)] : List FactorBlock).map factorBlockValue).prod) = 34877723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_821
      · exact prime_oneHundredTwentyDN_1931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34877723) ^ 17438861 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 34877723) ^ 3170702 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 34877723) ^ 42482 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 34877723) ^ 18062 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_36327593 : Nat.Prime 36327593 := by
  apply lucas_primality 36327593 (3 : ZMod 36327593)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (223, 1), (2909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (223, 1), (2909, 1)] : List FactorBlock).map factorBlockValue).prod) = 36327593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_223
      · exact prime_oneHundredTwentyDN_2909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 36327593) ^ 18163796 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 36327593) ^ 5189656 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 36327593) ^ 162904 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 36327593) ^ 12488 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_36502073 : Nat.Prime 36502073 := by
  apply lucas_primality 36502073 (3 : ZMod 36502073)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (83, 1), (54973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (83, 1), (54973, 1)] : List FactorBlock).map factorBlockValue).prod) = 36502073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_83
      · exact prime_oneHundredTwentyDN_54973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 36502073) ^ 18251036 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 36502073) ^ 439784 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 36502073) ^ 664 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_37721171 : Nat.Prime 37721171 := by
  apply lucas_primality 37721171 (2 : ZMod 37721171)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (130073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (130073, 1)] : List FactorBlock).map factorBlockValue).prod) = 37721171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_29
      · exact prime_oneHundredTwentyDN_130073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37721171) ^ 18860585 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 37721171) ^ 7544234 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 37721171) ^ 1300730 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 37721171) ^ 290 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_43813733 : Nat.Prime 43813733 := by
  apply lucas_primality 43813733 (2 : ZMod 43813733)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (254731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (254731, 1)] : List FactorBlock).map factorBlockValue).prod) = 43813733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_43
      · exact prime_oneHundredTwentyDN_254731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43813733) ^ 21906866 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 43813733) ^ 1018924 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 43813733) ^ 172 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_44805067 : Nat.Prime 44805067 := by
  apply lucas_primality 44805067 (2 : ZMod 44805067)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7467511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7467511, 1)] : List FactorBlock).map factorBlockValue).prod) = 44805067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7467511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 44805067) ^ 22402533 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 44805067) ^ 14935022 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 44805067) ^ 6 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_48503657 : Nat.Prime 48503657 := by
  apply lucas_primality 48503657 (3 : ZMod 48503657)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (41, 1), (43, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (41, 1), (43, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) = 48503657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_41
      · exact prime_oneHundredTwentyDN_43
      · exact prime_oneHundredTwentyDN_181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48503657) ^ 24251828 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 2552824 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 1183016 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 1127992 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 267976 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_50038073 : Nat.Prime 50038073 := by
  apply lucas_primality 50038073 (3 : ZMod 50038073)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (17, 1), (52561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (17, 1), (52561, 1)] : List FactorBlock).map factorBlockValue).prod) = 50038073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_52561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 50038073) ^ 25019036 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 50038073) ^ 7148296 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 50038073) ^ 2943416 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 50038073) ^ 952 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_51923327 : Nat.Prime 51923327 := by
  apply lucas_primality 51923327 (7 : ZMod 51923327)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (31, 1), (9203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (31, 1), (9203, 1)] : List FactorBlock).map factorBlockValue).prod) = 51923327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_31
      · exact prime_oneHundredTwentyDN_9203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 51923327) ^ 25961663 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 7417618 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 3994102 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 1674946 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 5642 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_52864081 : Nat.Prime 52864081 := by
  apply lucas_primality 52864081 (17 : ZMod 52864081)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) = 52864081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_11593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 52864081) ^ 26432040 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 17621360 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 10572816 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 2782320 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 4560 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_55413389 : Nat.Prime 55413389 := by
  apply lucas_primality 55413389 (2 : ZMod 55413389)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (179, 1), (193, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (179, 1), (193, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod) = 55413389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_179
      · exact prime_oneHundredTwentyDN_193
      · exact prime_oneHundredTwentyDN_401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55413389) ^ 27706694 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 55413389) ^ 309572 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 55413389) ^ 287116 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 55413389) ^ 138188 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_58296701 : Nat.Prime 58296701 := by
  apply lucas_primality 58296701 (10 : ZMod 58296701)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (11, 1), (67, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (11, 1), (67, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) = 58296701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_67
      · exact prime_oneHundredTwentyDN_113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 58296701) ^ 29148350 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 58296701) ^ 11659340 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 58296701) ^ 8328100 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 58296701) ^ 5299700 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 58296701) ^ 870100 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 58296701) ^ 515900 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_1811
      · exact prime_oneHundredTwentyDN_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_65339437 : Nat.Prime 65339437 := by
  apply lucas_primality 65339437 (2 : ZMod 65339437)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (359, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (359, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) = 65339437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_29
      · exact prime_oneHundredTwentyDN_359
      · exact prime_oneHundredTwentyDN_523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 65339437) ^ 32669718 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 65339437) ^ 21779812 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 65339437) ^ 2253084 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 65339437) ^ 182004 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 65339437) ^ 124932 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_66729107 : Nat.Prime 66729107 := by
  apply lucas_primality 66729107 (2 : ZMod 66729107)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (33364553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (33364553, 1)] : List FactorBlock).map factorBlockValue).prod) = 66729107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_33364553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 66729107) ^ 33364553 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 66729107) ^ 2 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_78358417 : Nat.Prime 78358417 := by
  apply lucas_primality 78358417 (10 : ZMod 78358417)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1632467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1632467, 1)] : List FactorBlock).map factorBlockValue).prod) = 78358417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_1632467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 78358417) ^ 39179208 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 78358417) ^ 26119472 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 78358417) ^ 48 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_82180489 : Nat.Prime 82180489 := by
  apply lucas_primality 82180489 (11 : ZMod 82180489)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (263399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (263399, 1)] : List FactorBlock).map factorBlockValue).prod) = 82180489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_263399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 82180489) ^ 41090244 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (11 : ZMod 82180489) ^ 27393496 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (11 : ZMod 82180489) ^ 6321576 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (11 : ZMod 82180489) ^ 312 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_88812211 : Nat.Prime 88812211 := by
  apply lucas_primality 88812211 (3 : ZMod 88812211)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (31, 1), (37, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (31, 1), (37, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) = 88812211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_29
      · exact prime_oneHundredTwentyDN_31
      · exact prime_oneHundredTwentyDN_37
      · exact prime_oneHundredTwentyDN_89
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88812211) ^ 44406105 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 29604070 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 17762442 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 3062490 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 2864910 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 2400330 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 997890 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_89916007 : Nat.Prime 89916007 := by
  apply lucas_primality 89916007 (3 : ZMod 89916007)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (14986001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (14986001, 1)] : List FactorBlock).map factorBlockValue).prod) = 89916007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_14986001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 89916007) ^ 44958003 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 89916007) ^ 29972002 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 89916007) ^ 6 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_92044709 : Nat.Prime 92044709 := by
  apply lucas_primality 92044709 (3 : ZMod 92044709)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (3287311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (3287311, 1)] : List FactorBlock).map factorBlockValue).prod) = 92044709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_3287311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 92044709) ^ 46022354 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 92044709) ^ 13149244 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 92044709) ^ 28 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_92103133 : Nat.Prime 92103133 := by
  apply lucas_primality 92103133 (5 : ZMod 92103133)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) = 92103133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_23
      · exact prime_oneHundredTwentyDN_1319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 92103133) ^ 46051566 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 30701044 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 8373012 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 4004484 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 69828 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_100076147 : Nat.Prime 100076147 := by
  apply lucas_primality 100076147 (2 : ZMod 100076147)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (50038073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (50038073, 1)] : List FactorBlock).map factorBlockValue).prod) = 100076147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_50038073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 100076147) ^ 50038073 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 100076147) ^ 2 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_110796689 : Nat.Prime 110796689 := by
  apply lucas_primality 110796689 (3 : ZMod 110796689)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (103, 1), (67231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (103, 1), (67231, 1)] : List FactorBlock).map factorBlockValue).prod) = 110796689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_103
      · exact prime_oneHundredTwentyDN_67231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 110796689) ^ 55398344 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 110796689) ^ 1075696 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 110796689) ^ 1648 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_111579263 : Nat.Prime 111579263 := by
  apply lucas_primality 111579263 (5 : ZMod 111579263)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (977, 1), (3359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (977, 1), (3359, 1)] : List FactorBlock).map factorBlockValue).prod) = 111579263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_977
      · exact prime_oneHundredTwentyDN_3359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 111579263) ^ 55789631 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 111579263) ^ 6563486 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 111579263) ^ 114206 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 111579263) ^ 33218 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_117195809 : Nat.Prime 117195809 := by
  apply lucas_primality 117195809 (3 : ZMod 117195809)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (491, 1), (7459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (491, 1), (7459, 1)] : List FactorBlock).map factorBlockValue).prod) = 117195809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_491
      · exact prime_oneHundredTwentyDN_7459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 117195809) ^ 58597904 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 117195809) ^ 238688 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 117195809) ^ 15712 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_122658787 : Nat.Prime 122658787 := by
  apply lucas_primality 122658787 (3 : ZMod 122658787)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (103, 1), (7351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (103, 1), (7351, 1)] : List FactorBlock).map factorBlockValue).prod) = 122658787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_103
      · exact prime_oneHundredTwentyDN_7351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 122658787) ^ 61329393 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 122658787) ^ 40886262 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 122658787) ^ 1190862 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 122658787) ^ 16686 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_152138407 : Nat.Prime 152138407 := by
  apply lucas_primality 152138407 (3 : ZMod 152138407)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (213079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (213079, 1)] : List FactorBlock).map factorBlockValue).prod) = 152138407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_213079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 152138407) ^ 76069203 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 152138407) ^ 50712802 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 152138407) ^ 21734058 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 152138407) ^ 8949318 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 152138407) ^ 714 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_186614149 : Nat.Prime 186614149 := by
  apply lucas_primality 186614149 (13 : ZMod 186614149)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (317371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (317371, 1)] : List FactorBlock).map factorBlockValue).prod) = 186614149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_317371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 186614149) ^ 93307074 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (13 : ZMod 186614149) ^ 62204716 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (13 : ZMod 186614149) ^ 26659164 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (13 : ZMod 186614149) ^ 588 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_195302473 : Nat.Prime 195302473 := by
  apply lucas_primality 195302473 (10 : ZMod 195302473)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (280607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (280607, 1)] : List FactorBlock).map factorBlockValue).prod) = 195302473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_29
      · exact prime_oneHundredTwentyDN_280607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 195302473) ^ 97651236 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 195302473) ^ 65100824 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 195302473) ^ 6734568 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 195302473) ^ 696 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_210430769 : Nat.Prime 210430769 := by
  apply lucas_primality 210430769 (3 : ZMod 210430769)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13151923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13151923, 1)] : List FactorBlock).map factorBlockValue).prod) = 210430769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_13151923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 210430769) ^ 105215384 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 210430769) ^ 16 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_213150073 : Nat.Prime 213150073 := by
  apply lucas_primality 213150073 (5 : ZMod 213150073)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (73, 1), (121661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (73, 1), (121661, 1)] : List FactorBlock).map factorBlockValue).prod) = 213150073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_73
      · exact prime_oneHundredTwentyDN_121661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 213150073) ^ 106575036 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 71050024 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 2919864 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 1752 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_233952713 : Nat.Prime 233952713 := by
  apply lucas_primality 233952713 (3 : ZMod 233952713)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (1777, 1), (2351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (1777, 1), (2351, 1)] : List FactorBlock).map factorBlockValue).prod) = 233952713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_1777
      · exact prime_oneHundredTwentyDN_2351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 233952713) ^ 116976356 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 233952713) ^ 33421816 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 233952713) ^ 131656 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 233952713) ^ 99512 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_240217849 : Nat.Prime 240217849 := by
  apply lucas_primality 240217849 (19 : ZMod 240217849)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (256643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (256643, 1)] : List FactorBlock).map factorBlockValue).prod) = 240217849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_256643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 240217849) ^ 120108924 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (19 : ZMod 240217849) ^ 80072616 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (19 : ZMod 240217849) ^ 18478296 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (19 : ZMod 240217849) ^ 936 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_248048113 : Nat.Prime 248048113 := by
  apply lucas_primality 248048113 (7 : ZMod 248048113)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (31, 1), (12823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (31, 1), (12823, 1)] : List FactorBlock).map factorBlockValue).prod) = 248048113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_31
      · exact prime_oneHundredTwentyDN_12823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 248048113) ^ 124024056 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 82682704 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 19080624 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 8001552 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 19344 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_302547061 : Nat.Prime 302547061 := by
  apply lucas_primality 302547061 (13 : ZMod 302547061)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (23, 1), (73079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (23, 1), (73079, 1)] : List FactorBlock).map factorBlockValue).prod) = 302547061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_23
      · exact prime_oneHundredTwentyDN_73079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 302547061) ^ 151273530 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (13 : ZMod 302547061) ^ 100849020 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (13 : ZMod 302547061) ^ 60509412 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (13 : ZMod 302547061) ^ 13154220 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (13 : ZMod 302547061) ^ 4140 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_316566433 : Nat.Prime 316566433 := by
  apply lucas_primality 316566433 (5 : ZMod 316566433)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (7, 1), (13, 1), (47, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (7, 1), (13, 1), (47, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) = 316566433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_47
      · exact prime_oneHundredTwentyDN_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 316566433) ^ 158283216 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 316566433) ^ 105522144 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 316566433) ^ 45223776 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 316566433) ^ 24351264 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 316566433) ^ 6735456 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 316566433) ^ 1231776 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_337303277 : Nat.Prime 337303277 := by
  apply lucas_primality 337303277 (2 : ZMod 337303277)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (4438201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (4438201, 1)] : List FactorBlock).map factorBlockValue).prod) = 337303277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_4438201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 337303277) ^ 168651638 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 337303277) ^ 17752804 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 337303277) ^ 76 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_353497423 : Nat.Prime 353497423 := by
  apply lucas_primality 353497423 (5 : ZMod 353497423)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (1151, 1), (3011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (1151, 1), (3011, 1)] : List FactorBlock).map factorBlockValue).prod) = 353497423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_1151
      · exact prime_oneHundredTwentyDN_3011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 353497423) ^ 176748711 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 353497423) ^ 117832474 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 353497423) ^ 20793966 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 353497423) ^ 307122 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 353497423) ^ 117402 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_362051087 : Nat.Prime 362051087 := by
  apply lucas_primality 362051087 (5 : ZMod 362051087)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) = 362051087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_12539
      · exact prime_oneHundredTwentyDN_14437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 362051087) ^ 181025543 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 28874 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 25078 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_370615897 : Nat.Prime 370615897 := by
  apply lucas_primality 370615897 (5 : ZMod 370615897)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (701, 1), (1049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (701, 1), (1049, 1)] : List FactorBlock).map factorBlockValue).prod) = 370615897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_701
      · exact prime_oneHundredTwentyDN_1049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 370615897) ^ 185307948 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 370615897) ^ 123538632 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 370615897) ^ 52945128 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 370615897) ^ 528696 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 370615897) ^ 353304 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_413346319 : Nat.Prime 413346319 := by
  apply lucas_primality 413346319 (3 : ZMod 413346319)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (894689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (894689, 1)] : List FactorBlock).map factorBlockValue).prod) = 413346319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_894689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 413346319) ^ 206673159 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 413346319) ^ 137782106 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 413346319) ^ 59049474 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 413346319) ^ 37576938 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 413346319) ^ 462 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_432433721 : Nat.Prime 432433721 := by
  apply lucas_primality 432433721 (3 : ZMod 432433721)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (1289, 1), (8387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (1289, 1), (8387, 1)] : List FactorBlock).map factorBlockValue).prod) = 432433721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_1289
      · exact prime_oneHundredTwentyDN_8387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 432433721) ^ 216216860 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 432433721) ^ 86486744 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 432433721) ^ 335480 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 432433721) ^ 51560 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_456031721 : Nat.Prime 456031721 := by
  apply lucas_primality 456031721 (3 : ZMod 456031721)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11400793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11400793, 1)] : List FactorBlock).map factorBlockValue).prod) = 456031721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_11400793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 456031721) ^ 228015860 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 456031721) ^ 91206344 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 456031721) ^ 40 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_466587599 : Nat.Prime 466587599 := by
  apply lucas_primality 466587599 (14 : ZMod 466587599)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (67, 1), (183263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (67, 1), (183263, 1)] : List FactorBlock).map factorBlockValue).prod) = 466587599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_67
      · exact prime_oneHundredTwentyDN_183263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 466587599) ^ 233293799 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (14 : ZMod 466587599) ^ 24557242 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (14 : ZMod 466587599) ^ 6963994 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (14 : ZMod 466587599) ^ 2546 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_470150503 : Nat.Prime 470150503 := by
  apply lucas_primality 470150503 (3 : ZMod 470150503)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (78358417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (78358417, 1)] : List FactorBlock).map factorBlockValue).prod) = 470150503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_78358417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 470150503) ^ 235075251 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 470150503) ^ 156716834 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 470150503) ^ 6 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_470912483 : Nat.Prime 470912483 := by
  apply lucas_primality 470912483 (2 : ZMod 470912483)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (2160149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (2160149, 1)] : List FactorBlock).map factorBlockValue).prod) = 470912483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_109
      · exact prime_oneHundredTwentyDN_2160149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 470912483) ^ 235456241 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 470912483) ^ 4320298 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 470912483) ^ 218 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_487066871 : Nat.Prime 487066871 := by
  apply lucas_primality 487066871 (7 : ZMod 487066871)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1907, 1), (25541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1907, 1), (25541, 1)] : List FactorBlock).map factorBlockValue).prod) = 487066871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_1907
      · exact prime_oneHundredTwentyDN_25541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 487066871) ^ 243533435 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 487066871) ^ 97413374 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 487066871) ^ 255410 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 487066871) ^ 19070 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_559319647 : Nat.Prime 559319647 := by
  apply lucas_primality 559319647 (3 : ZMod 559319647)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (59, 1), (33617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (59, 1), (33617, 1)] : List FactorBlock).map factorBlockValue).prod) = 559319647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_47
      · exact prime_oneHundredTwentyDN_59
      · exact prime_oneHundredTwentyDN_33617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 559319647) ^ 279659823 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 186439882 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 11900418 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 9479994 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 16638 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_612972127 : Nat.Prime 612972127 := by
  apply lucas_primality 612972127 (5 : ZMod 612972127)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 2), (23, 1), (8761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 2), (23, 1), (8761, 1)] : List FactorBlock).map factorBlockValue).prod) = 612972127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_23
      · exact prime_oneHundredTwentyDN_8761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 612972127) ^ 306486063 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 612972127) ^ 204324042 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 612972127) ^ 47151702 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 612972127) ^ 26650962 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 612972127) ^ 69966 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_61
      · exact prime_oneHundredTwentyDN_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_679311571 : Nat.Prime 679311571 := by
  apply lucas_primality 679311571 (2 : ZMod 679311571)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (127, 1), (25471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (127, 1), (25471, 1)] : List FactorBlock).map factorBlockValue).prod) = 679311571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_127
      · exact prime_oneHundredTwentyDN_25471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 679311571) ^ 339655785 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 226437190 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 135862314 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 97044510 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 5348910 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 26670 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_711437231 : Nat.Prime 711437231 := by
  apply lucas_primality 711437231 (7 : ZMod 711437231)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (10163389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (10163389, 1)] : List FactorBlock).map factorBlockValue).prod) = 711437231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_10163389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 711437231) ^ 355718615 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 711437231) ^ 142287446 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 711437231) ^ 101633890 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 711437231) ^ 70 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_17203
      · exact prime_oneHundredTwentyDN_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_765941959 : Nat.Prime 765941959 := by
  apply lucas_primality 765941959 (3 : ZMod 765941959)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (1150063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (1150063, 1)] : List FactorBlock).map factorBlockValue).prod) = 765941959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_37
      · exact prime_oneHundredTwentyDN_1150063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 765941959) ^ 382970979 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 765941959) ^ 255313986 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 765941959) ^ 20701134 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 765941959) ^ 666 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_886666177 : Nat.Prime 886666177 := by
  apply lucas_primality 886666177 (10 : ZMod 886666177)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 5), (11, 1), (71, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 5), (11, 1), (71, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) = 886666177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_71
      · exact prime_oneHundredTwentyDN_73
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 886666177) ^ 443333088 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 886666177) ^ 295555392 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 886666177) ^ 80606016 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 886666177) ^ 12488256 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 886666177) ^ 12146112 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_905401751 : Nat.Prime 905401751 := by
  apply lucas_primality 905401751 (7 : ZMod 905401751)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (11, 1), (29, 1), (11353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (11, 1), (29, 1), (11353, 1)] : List FactorBlock).map factorBlockValue).prod) = 905401751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_29
      · exact prime_oneHundredTwentyDN_11353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 905401751) ^ 452700875 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 905401751) ^ 181080350 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 905401751) ^ 82309250 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 905401751) ^ 31220750 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 905401751) ^ 79750 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_905681131 : Nat.Prime 905681131 := by
  apply lucas_primality 905681131 (3 : ZMod 905681131)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (30189371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (30189371, 1)] : List FactorBlock).map factorBlockValue).prod) = 905681131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_30189371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 905681131) ^ 452840565 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 905681131) ^ 301893710 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 905681131) ^ 181136226 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 905681131) ^ 30 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1101731381 : Nat.Prime 1101731381 := by
  apply lucas_primality 1101731381 (3 : ZMod 1101731381)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (43, 1), (1281083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (43, 1), (1281083, 1)] : List FactorBlock).map factorBlockValue).prod) = 1101731381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_43
      · exact prime_oneHundredTwentyDN_1281083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1101731381) ^ 550865690 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1101731381) ^ 220346276 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1101731381) ^ 25621660 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1101731381) ^ 860 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1143177577 : Nat.Prime 1143177577 := by
  apply lucas_primality 1143177577 (5 : ZMod 1143177577)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (61, 1), (25189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (61, 1), (25189, 1)] : List FactorBlock).map factorBlockValue).prod) = 1143177577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_31
      · exact prime_oneHundredTwentyDN_61
      · exact prime_oneHundredTwentyDN_25189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1143177577) ^ 571588788 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1143177577) ^ 381059192 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1143177577) ^ 36876696 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1143177577) ^ 18740616 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1143177577) ^ 45384 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1189754491 : Nat.Prime 1189754491 := by
  apply lucas_primality 1189754491 (2 : ZMod 1189754491)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2243, 1), (17681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2243, 1), (17681, 1)] : List FactorBlock).map factorBlockValue).prod) = 1189754491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_2243
      · exact prime_oneHundredTwentyDN_17681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1189754491) ^ 594877245 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1189754491) ^ 396584830 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1189754491) ^ 237950898 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1189754491) ^ 530430 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1189754491) ^ 67290 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1299989947 : Nat.Prime 1299989947 := by
  apply lucas_primality 1299989947 (2 : ZMod 1299989947)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1299989947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_23
      · exact prime_oneHundredTwentyDN_1667
      · exact prime_oneHundredTwentyDN_5651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1299989947) ^ 649994973 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 433329982 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 56521302 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 779838 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 230046 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1537396151 : Nat.Prime 1537396151 := by
  apply lucas_primality 1537396151 (13 : ZMod 1537396151)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (30747923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (30747923, 1)] : List FactorBlock).map factorBlockValue).prod) = 1537396151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_30747923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 1537396151) ^ 768698075 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (13 : ZMod 1537396151) ^ 307479230 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (13 : ZMod 1537396151) ^ 50 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1861975811 : Nat.Prime 1861975811 := by
  apply lucas_primality 1861975811 (2 : ZMod 1861975811)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (8095547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (8095547, 1)] : List FactorBlock).map factorBlockValue).prod) = 1861975811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_23
      · exact prime_oneHundredTwentyDN_8095547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1861975811) ^ 930987905 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1861975811) ^ 372395162 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1861975811) ^ 80955470 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1861975811) ^ 230 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_2149724321 : Nat.Prime 2149724321 := by
  apply lucas_primality 2149724321 (3 : ZMod 2149724321)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (149, 1), (90173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (149, 1), (90173, 1)] : List FactorBlock).map factorBlockValue).prod) = 2149724321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_149
      · exact prime_oneHundredTwentyDN_90173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2149724321) ^ 1074862160 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2149724321) ^ 429944864 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2149724321) ^ 14427680 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2149724321) ^ 23840 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_2213346269 : Nat.Prime 2213346269 := by
  apply lucas_primality 2213346269 (2 : ZMod 2213346269)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (11292583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (11292583, 1)] : List FactorBlock).map factorBlockValue).prod) = 2213346269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_11292583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2213346269) ^ 1106673134 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2213346269) ^ 316192324 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2213346269) ^ 196 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_2301053693 : Nat.Prime 2301053693 := by
  apply lucas_primality 2301053693 (2 : ZMod 2301053693)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (82180489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (82180489, 1)] : List FactorBlock).map factorBlockValue).prod) = 2301053693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_82180489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2301053693) ^ 1150526846 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2301053693) ^ 328721956 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2301053693) ^ 28 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_2372670067 : Nat.Prime 2372670067 := by
  apply lucas_primality 2372670067 (3 : ZMod 2372670067)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (37, 1), (822131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (37, 1), (822131, 1)] : List FactorBlock).map factorBlockValue).prod) = 2372670067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_37
      · exact prime_oneHundredTwentyDN_822131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2372670067) ^ 1186335033 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2372670067) ^ 790890022 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2372670067) ^ 182513082 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2372670067) ^ 64126218 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2372670067) ^ 2886 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_47
      · exact prime_oneHundredTwentyDN_71
      · exact prime_oneHundredTwentyDN_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_2533330567 : Nat.Prime 2533330567 := by
  apply lucas_primality 2533330567 (5 : ZMod 2533330567)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (211, 1), (5701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (211, 1), (5701, 1)] : List FactorBlock).map factorBlockValue).prod) = 2533330567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_211
      · exact prime_oneHundredTwentyDN_5701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2533330567) ^ 1266665283 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2533330567) ^ 844443522 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2533330567) ^ 194871582 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2533330567) ^ 12006306 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2533330567) ^ 444366 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_2655560587 : Nat.Prime 2655560587 := by
  apply lucas_primality 2655560587 (2 : ZMod 2655560587)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (179, 1), (50461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (179, 1), (50461, 1)] : List FactorBlock).map factorBlockValue).prod) = 2655560587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_179
      · exact prime_oneHundredTwentyDN_50461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2655560587) ^ 1327780293 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2655560587) ^ 885186862 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2655560587) ^ 379365798 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2655560587) ^ 14835534 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2655560587) ^ 52626 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_3165480589 : Nat.Prime 3165480589 := by
  apply lucas_primality 3165480589 (6 : ZMod 3165480589)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (127, 1), (1249, 1), (1663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (127, 1), (1249, 1), (1663, 1)] : List FactorBlock).map factorBlockValue).prod) = 3165480589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_127
      · exact prime_oneHundredTwentyDN_1249
      · exact prime_oneHundredTwentyDN_1663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3165480589) ^ 1582740294 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3165480589) ^ 1055160196 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3165480589) ^ 24925044 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3165480589) ^ 2534412 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3165480589) ^ 1903476 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_3364231441 : Nat.Prime 3364231441 := by
  apply lucas_primality 3364231441 (19 : ZMod 3364231441)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (1637, 1), (8563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (1637, 1), (8563, 1)] : List FactorBlock).map factorBlockValue).prod) = 3364231441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_1637
      · exact prime_oneHundredTwentyDN_8563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 3364231441) ^ 1682115720 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (19 : ZMod 3364231441) ^ 1121410480 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (19 : ZMod 3364231441) ^ 672846288 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (19 : ZMod 3364231441) ^ 2055120 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (19 : ZMod 3364231441) ^ 392880 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_4171314503 : Nat.Prime 4171314503 := by
  apply lucas_primality 4171314503 (5 : ZMod 4171314503)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (48503657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (48503657, 1)] : List FactorBlock).map factorBlockValue).prod) = 4171314503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_43
      · exact prime_oneHundredTwentyDN_48503657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4171314503) ^ 2085657251 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 4171314503) ^ 97007314 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 4171314503) ^ 86 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_4980897683 : Nat.Prime 4980897683 := by
  apply lucas_primality 4980897683 (2 : ZMod 4980897683)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1171, 1), (2126771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1171, 1), (2126771, 1)] : List FactorBlock).map factorBlockValue).prod) = 4980897683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_1171
      · exact prime_oneHundredTwentyDN_2126771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4980897683) ^ 2490448841 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4980897683) ^ 4253542 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4980897683) ^ 2342 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_6008710237 : Nat.Prime 6008710237 := by
  apply lucas_primality 6008710237 (5 : ZMod 6008710237)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3001, 1), (166853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3001, 1), (166853, 1)] : List FactorBlock).map factorBlockValue).prod) = 6008710237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_3001
      · exact prime_oneHundredTwentyDN_166853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6008710237) ^ 3004355118 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 6008710237) ^ 2002903412 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 6008710237) ^ 2002236 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 6008710237) ^ 36012 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_31
      · exact prime_oneHundredTwentyDN_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_7521275257 : Nat.Prime 7521275257 := by
  apply lucas_primality 7521275257 (5 : ZMod 7521275257)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (5179, 1), (5501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (5179, 1), (5501, 1)] : List FactorBlock).map factorBlockValue).prod) = 7521275257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_5179
      · exact prime_oneHundredTwentyDN_5501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7521275257) ^ 3760637628 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7521275257) ^ 2507091752 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7521275257) ^ 683752296 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7521275257) ^ 1452264 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7521275257) ^ 1367256 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_7847598419 : Nat.Prime 7847598419 := by
  apply lucas_primality 7847598419 (2 : ZMod 7847598419)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (29, 1), (12300311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (29, 1), (12300311, 1)] : List FactorBlock).map factorBlockValue).prod) = 7847598419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_29
      · exact prime_oneHundredTwentyDN_12300311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7847598419) ^ 3923799209 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7847598419) ^ 713418038 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7847598419) ^ 270606842 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7847598419) ^ 638 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_8380149067 : Nat.Prime 8380149067 := by
  apply lucas_primality 8380149067 (2 : ZMod 8380149067)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (191, 1), (2437507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (191, 1), (2437507, 1)] : List FactorBlock).map factorBlockValue).prod) = 8380149067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_191
      · exact prime_oneHundredTwentyDN_2437507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8380149067) ^ 4190074533 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8380149067) ^ 2793383022 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8380149067) ^ 43875126 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8380149067) ^ 3438 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_10089149659 : Nat.Prime 10089149659 := by
  apply lucas_primality 10089149659 (3 : ZMod 10089149659)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (240217849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (240217849, 1)] : List FactorBlock).map factorBlockValue).prod) = 10089149659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_240217849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10089149659) ^ 5044574829 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 10089149659) ^ 3363049886 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 10089149659) ^ 1441307094 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 10089149659) ^ 42 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_10868173573 : Nat.Prime 10868173573 := by
  apply lucas_primality 10868173573 (2 : ZMod 10868173573)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (905681131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (905681131, 1)] : List FactorBlock).map factorBlockValue).prod) = 10868173573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_905681131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10868173573) ^ 5434086786 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10868173573) ^ 3622724524 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10868173573) ^ 12 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_11129533489 : Nat.Prime 11129533489 := by
  apply lucas_primality 11129533489 (11 : ZMod 11129533489)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (653, 1), (13151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (653, 1), (13151, 1)] : List FactorBlock).map factorBlockValue).prod) = 11129533489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_653
      · exact prime_oneHundredTwentyDN_13151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 11129533489) ^ 5564766744 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (11 : ZMod 11129533489) ^ 3709844496 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (11 : ZMod 11129533489) ^ 17043696 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (11 : ZMod 11129533489) ^ 846288 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_11953240339 : Nat.Prime 11953240339 := by
  apply lucas_primality 11953240339 (3 : ZMod 11953240339)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (31, 1), (4943441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (31, 1), (4943441, 1)] : List FactorBlock).map factorBlockValue).prod) = 11953240339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_31
      · exact prime_oneHundredTwentyDN_4943441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11953240339) ^ 5976620169 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11953240339) ^ 3984413446 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11953240339) ^ 919480026 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11953240339) ^ 385588398 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11953240339) ^ 2418 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_12446797171 : Nat.Prime 12446797171 := by
  apply lucas_primality 12446797171 (7 : ZMod 12446797171)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (433, 1), (958183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (433, 1), (958183, 1)] : List FactorBlock).map factorBlockValue).prod) = 12446797171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_433
      · exact prime_oneHundredTwentyDN_958183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 12446797171) ^ 6223398585 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 12446797171) ^ 4148932390 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 12446797171) ^ 2489359434 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 12446797171) ^ 28745490 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 12446797171) ^ 12990 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_14757462491 : Nat.Prime 14757462491 := by
  apply lucas_primality 14757462491 (2 : ZMod 14757462491)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (101, 1), (809, 1), (18061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (101, 1), (809, 1), (18061, 1)] : List FactorBlock).map factorBlockValue).prod) = 14757462491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_101
      · exact prime_oneHundredTwentyDN_809
      · exact prime_oneHundredTwentyDN_18061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14757462491) ^ 7378731245 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 14757462491) ^ 2951492498 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 14757462491) ^ 146113490 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 14757462491) ^ 18241610 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 14757462491) ^ 817090 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_23096547757 : Nat.Prime 23096547757 := by
  apply lucas_primality 23096547757 (5 : ZMod 23096547757)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (79, 1), (163, 1), (49823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (79, 1), (163, 1), (49823, 1)] : List FactorBlock).map factorBlockValue).prod) = 23096547757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_79
      · exact prime_oneHundredTwentyDN_163
      · exact prime_oneHundredTwentyDN_49823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 23096547757) ^ 11548273878 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 7698849252 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 292361364 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 141696612 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 463572 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_25734798431 : Nat.Prime 25734798431 := by
  apply lucas_primality 25734798431 (17 : ZMod 25734798431)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (233952713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (233952713, 1)] : List FactorBlock).map factorBlockValue).prod) = 25734798431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_233952713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 25734798431) ^ 12867399215 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 25734798431) ^ 5146959686 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 25734798431) ^ 2339527130 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 25734798431) ^ 110 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_26752207429 : Nat.Prime 26752207429 := by
  apply lucas_primality 26752207429 (2 : ZMod 26752207429)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (4621, 1), (160813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (4621, 1), (160813, 1)] : List FactorBlock).map factorBlockValue).prod) = 26752207429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_4621
      · exact prime_oneHundredTwentyDN_160813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26752207429) ^ 13376103714 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 8917402476 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 5789268 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 166356 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_26896283387 : Nat.Prime 26896283387 := by
  apply lucas_primality 26896283387 (2 : ZMod 26896283387)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (51923327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (51923327, 1)] : List FactorBlock).map factorBlockValue).prod) = 26896283387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_37
      · exact prime_oneHundredTwentyDN_51923327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26896283387) ^ 13448141693 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 26896283387) ^ 3842326198 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 26896283387) ^ 726926578 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 26896283387) ^ 518 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_29319813199 : Nat.Prime 29319813199 := by
  apply lucas_primality 29319813199 (3 : ZMod 29319813199)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (17, 1), (7370491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (17, 1), (7370491, 1)] : List FactorBlock).map factorBlockValue).prod) = 29319813199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_7370491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 29319813199) ^ 14659906599 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 29319813199) ^ 9773271066 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 29319813199) ^ 2255370246 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 29319813199) ^ 1724694894 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 29319813199) ^ 3978 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_30129387137 : Nat.Prime 30129387137 := by
  apply lucas_primality 30129387137 (3 : ZMod 30129387137)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (29, 1), (8116753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (29, 1), (8116753, 1)] : List FactorBlock).map factorBlockValue).prod) = 30129387137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_29
      · exact prime_oneHundredTwentyDN_8116753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 30129387137) ^ 15064693568 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 30129387137) ^ 1038944384 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 30129387137) ^ 3712 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_31763054933 : Nat.Prime 31763054933 := by
  apply lucas_primality 31763054933 (2 : ZMod 31763054933)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (66729107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (66729107, 1)] : List FactorBlock).map factorBlockValue).prod) = 31763054933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_66729107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31763054933) ^ 15881527466 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 31763054933) ^ 4537579276 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 31763054933) ^ 1868414996 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 31763054933) ^ 476 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_33323112871 : Nat.Prime 33323112871 := by
  apply lucas_primality 33323112871 (3 : ZMod 33323112871)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (65339437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (65339437, 1)] : List FactorBlock).map factorBlockValue).prod) = 33323112871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_65339437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33323112871) ^ 16661556435 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 33323112871) ^ 11107704290 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 33323112871) ^ 6664622574 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 33323112871) ^ 1960183110 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 33323112871) ^ 510 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_35264271901 : Nat.Prime 35264271901 := by
  apply lucas_primality 35264271901 (7 : ZMod 35264271901)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (11, 1), (13, 1), (822011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (11, 1), (13, 1), (822011, 1)] : List FactorBlock).map factorBlockValue).prod) = 35264271901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_822011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 35264271901) ^ 17632135950 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 35264271901) ^ 11754757300 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 35264271901) ^ 7052854380 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 35264271901) ^ 3205842900 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 35264271901) ^ 2712636300 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 35264271901) ^ 42900 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_39041767819 : Nat.Prime 39041767819 := by
  apply lucas_primality 39041767819 (2 : ZMod 39041767819)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (37, 1), (2548751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (37, 1), (2548751, 1)] : List FactorBlock).map factorBlockValue).prod) = 39041767819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_23
      · exact prime_oneHundredTwentyDN_37
      · exact prime_oneHundredTwentyDN_2548751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39041767819) ^ 19520883909 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 39041767819) ^ 13013922606 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 39041767819) ^ 1697468166 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 39041767819) ^ 1055182914 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 39041767819) ^ 15318 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_43866235967 : Nat.Prime 43866235967 := by
  apply lucas_primality 43866235967 (5 : ZMod 43866235967)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (73, 1), (1787, 1), (24019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (73, 1), (1787, 1), (24019, 1)] : List FactorBlock).map factorBlockValue).prod) = 43866235967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_73
      · exact prime_oneHundredTwentyDN_1787
      · exact prime_oneHundredTwentyDN_24019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 43866235967) ^ 21933117983 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 43866235967) ^ 6266605138 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 43866235967) ^ 600907342 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 43866235967) ^ 24547418 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 43866235967) ^ 1826314 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_45225709423 : Nat.Prime 45225709423 := by
  apply lucas_primality 45225709423 (5 : ZMod 45225709423)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (16631, 1), (453227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (16631, 1), (453227, 1)] : List FactorBlock).map factorBlockValue).prod) = 45225709423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_16631
      · exact prime_oneHundredTwentyDN_453227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 45225709423) ^ 22612854711 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 45225709423) ^ 15075236474 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 45225709423) ^ 2719362 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 45225709423) ^ 99786 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_46916828279 : Nat.Prime 46916828279 := by
  apply lucas_primality 46916828279 (17 : ZMod 46916828279)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1031, 1), (1901, 1), (11969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1031, 1), (1901, 1), (11969, 1)] : List FactorBlock).map factorBlockValue).prod) = 46916828279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_1031
      · exact prime_oneHundredTwentyDN_1901
      · exact prime_oneHundredTwentyDN_11969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 46916828279) ^ 23458414139 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 46916828279) ^ 45506138 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 46916828279) ^ 24680078 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 46916828279) ^ 3919862 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_47591935099 : Nat.Prime 47591935099 := by
  apply lucas_primality 47591935099 (2 : ZMod 47591935099)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (466587599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (466587599, 1)] : List FactorBlock).map factorBlockValue).prod) = 47591935099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_466587599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47591935099) ^ 23795967549 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 47591935099) ^ 15863978366 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 47591935099) ^ 2799525594 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 47591935099) ^ 102 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_52586168543 : Nat.Prime 52586168543 := by
  apply lucas_primality 52586168543 (5 : ZMod 52586168543)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (1143177577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (1143177577, 1)] : List FactorBlock).map factorBlockValue).prod) = 52586168543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_23
      · exact prime_oneHundredTwentyDN_1143177577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 52586168543) ^ 26293084271 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 52586168543) ^ 2286355154 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 52586168543) ^ 46 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_56591413171 : Nat.Prime 56591413171 := by
  apply lucas_primality 56591413171 (2 : ZMod 56591413171)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (41, 1), (2421541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (41, 1), (2421541, 1)] : List FactorBlock).map factorBlockValue).prod) = 56591413171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_41
      · exact prime_oneHundredTwentyDN_2421541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56591413171) ^ 28295706585 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 56591413171) ^ 18863804390 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 56591413171) ^ 11318282634 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 56591413171) ^ 2978495430 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 56591413171) ^ 1380278370 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 56591413171) ^ 23370 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_70877835001 : Nat.Prime 70877835001 := by
  apply lucas_primality 70877835001 (17 : ZMod 70877835001)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 4), (7, 1), (23, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 4), (7, 1), (23, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) = 70877835001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_23
      · exact prime_oneHundredTwentyDN_1087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 70877835001) ^ 35438917500 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 70877835001) ^ 23625945000 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 70877835001) ^ 14175567000 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 70877835001) ^ 10125405000 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 70877835001) ^ 3081645000 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 70877835001) ^ 65205000 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_74775919583 : Nat.Prime 74775919583 := by
  apply lucas_primality 74775919583 (5 : ZMod 74775919583)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (43, 1), (9554807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (43, 1), (9554807, 1)] : List FactorBlock).map factorBlockValue).prod) = 74775919583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_43
      · exact prime_oneHundredTwentyDN_9554807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 74775919583) ^ 37387959791 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 10682274226 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 5751993814 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 1738974874 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 7826 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_100059262279 : Nat.Prime 100059262279 := by
  apply lucas_primality 100059262279 (3 : ZMod 100059262279)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (31, 1), (47, 1), (602411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (31, 1), (47, 1), (602411, 1)] : List FactorBlock).map factorBlockValue).prod) = 100059262279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_31
      · exact prime_oneHundredTwentyDN_47
      · exact prime_oneHundredTwentyDN_602411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 100059262279) ^ 50029631139 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 100059262279) ^ 33353087426 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 100059262279) ^ 5266276962 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 100059262279) ^ 3227718138 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 100059262279) ^ 2128920474 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 100059262279) ^ 166098 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_104079456961 : Nat.Prime 104079456961 := by
  apply lucas_primality 104079456961 (17 : ZMod 104079456961)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (863, 1), (125627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (863, 1), (125627, 1)] : List FactorBlock).map factorBlockValue).prod) = 104079456961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_863
      · exact prime_oneHundredTwentyDN_125627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 104079456961) ^ 52039728480 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 104079456961) ^ 34693152320 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 104079456961) ^ 20815891392 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 104079456961) ^ 120601920 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 104079456961) ^ 828480 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_120055286693 : Nat.Prime 120055286693 := by
  apply lucas_primality 120055286693 (2 : ZMod 120055286693)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (248048113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (248048113, 1)] : List FactorBlock).map factorBlockValue).prod) = 120055286693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_248048113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 120055286693) ^ 60027643346 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 120055286693) ^ 10914116972 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 120055286693) ^ 484 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_140168308879 : Nat.Prime 140168308879 := by
  apply lucas_primality 140168308879 (3 : ZMod 140168308879)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) = 140168308879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_853
      · exact prime_oneHundredTwentyDN_702239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 140168308879) ^ 70084154439 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 46722769626 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 10782177606 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 164323926 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 199602 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_172177267453 : Nat.Prime 172177267453 := by
  apply lucas_primality 172177267453 (5 : ZMod 172177267453)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (47, 1), (17957579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (47, 1), (17957579, 1)] : List FactorBlock).map factorBlockValue).prod) = 172177267453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_47
      · exact prime_oneHundredTwentyDN_17957579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 172177267453) ^ 86088633726 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 172177267453) ^ 57392422484 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 172177267453) ^ 10128074556 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 172177267453) ^ 3663346116 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 172177267453) ^ 9588 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_220796972729 : Nat.Prime 220796972729 := by
  apply lucas_primality 220796972729 (3 : ZMod 220796972729)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4547, 1), (6069853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4547, 1), (6069853, 1)] : List FactorBlock).map factorBlockValue).prod) = 220796972729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_4547
      · exact prime_oneHundredTwentyDN_6069853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 220796972729) ^ 110398486364 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 220796972729) ^ 48558824 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 220796972729) ^ 36376 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_222133410637 : Nat.Prime 222133410637 := by
  apply lucas_primality 222133410637 (5 : ZMod 222133410637)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (373, 1), (3449, 1), (14389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (373, 1), (3449, 1), (14389, 1)] : List FactorBlock).map factorBlockValue).prod) = 222133410637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_373
      · exact prime_oneHundredTwentyDN_3449
      · exact prime_oneHundredTwentyDN_14389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 222133410637) ^ 111066705318 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 74044470212 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 595531932 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 64405164 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 15437724 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_263872406687 : Nat.Prime 263872406687 := by
  apply lucas_primality 263872406687 (5 : ZMod 263872406687)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (101, 1), (186614149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (101, 1), (186614149, 1)] : List FactorBlock).map factorBlockValue).prod) = 263872406687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_101
      · exact prime_oneHundredTwentyDN_186614149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 263872406687) ^ 131936203343 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 263872406687) ^ 37696058098 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 263872406687) ^ 2612598086 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 263872406687) ^ 1414 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_276099113611 : Nat.Prime 276099113611 := by
  apply lucas_primality 276099113611 (2 : ZMod 276099113611)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 1), (29, 1), (71, 1), (87643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 1), (29, 1), (71, 1), (87643, 1)] : List FactorBlock).map factorBlockValue).prod) = 276099113611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_29
      · exact prime_oneHundredTwentyDN_71
      · exact prime_oneHundredTwentyDN_87643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 276099113611) ^ 138049556805 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 276099113611) ^ 92033037870 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 276099113611) ^ 55219822722 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 276099113611) ^ 16241124330 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 276099113611) ^ 9520659090 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 276099113611) ^ 3888719910 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 276099113611) ^ 3150270 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_288836296843 : Nat.Prime 288836296843 := by
  apply lucas_primality 288836296843 (2 : ZMod 288836296843)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (523, 1), (92044709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (523, 1), (92044709, 1)] : List FactorBlock).map factorBlockValue).prod) = 288836296843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_523
      · exact prime_oneHundredTwentyDN_92044709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 288836296843) ^ 144418148421 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 288836296843) ^ 96278765614 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 288836296843) ^ 552268254 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 288836296843) ^ 3138 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_371214717911 : Nat.Prime 371214717911 := by
  apply lucas_primality 371214717911 (7 : ZMod 371214717911)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (905401751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (905401751, 1)] : List FactorBlock).map factorBlockValue).prod) = 371214717911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_41
      · exact prime_oneHundredTwentyDN_905401751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 371214717911) ^ 185607358955 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 371214717911) ^ 74242943582 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 371214717911) ^ 9054017510 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 371214717911) ^ 410 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_446011079209 : Nat.Prime 446011079209 := by
  apply lucas_primality 446011079209 (7 : ZMod 446011079209)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (829, 1), (723133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (829, 1), (723133, 1)] : List FactorBlock).map factorBlockValue).prod) = 446011079209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_31
      · exact prime_oneHundredTwentyDN_829
      · exact prime_oneHundredTwentyDN_723133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 446011079209) ^ 223005539604 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 446011079209) ^ 148670359736 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 446011079209) ^ 14387454168 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 446011079209) ^ 538010952 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 446011079209) ^ 616776 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_518096174909 : Nat.Prime 518096174909 := by
  apply lucas_primality 518096174909 (2 : ZMod 518096174909)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (19, 1), (227, 1), (2310083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (19, 1), (227, 1), (2310083, 1)] : List FactorBlock).map factorBlockValue).prod) = 518096174909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_227
      · exact prime_oneHundredTwentyDN_2310083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 518096174909) ^ 259048087454 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 518096174909) ^ 39853551916 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 518096174909) ^ 27268219732 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 518096174909) ^ 2282362004 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 518096174909) ^ 224276 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_626696252953 : Nat.Prime 626696252953 := by
  apply lucas_primality 626696252953 (5 : ZMod 626696252953)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (11, 1), (43, 1), (1126649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (11, 1), (43, 1), (1126649, 1)] : List FactorBlock).map factorBlockValue).prod) = 626696252953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_43
      · exact prime_oneHundredTwentyDN_1126649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 626696252953) ^ 313348126476 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 626696252953) ^ 208898750984 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 626696252953) ^ 89528036136 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 626696252953) ^ 56972386632 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 626696252953) ^ 14574331464 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 626696252953) ^ 556248 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_749523766273 : Nat.Prime 749523766273 := by
  apply lucas_primality 749523766273 (5 : ZMod 749523766273)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (47, 1), (821, 1), (6323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (47, 1), (821, 1), (6323, 1)] : List FactorBlock).map factorBlockValue).prod) = 749523766273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_47
      · exact prime_oneHundredTwentyDN_821
      · exact prime_oneHundredTwentyDN_6323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 749523766273) ^ 374761883136 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 249841255424 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 15947314176 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 912940032 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 118539264 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1022058768707 : Nat.Prime 1022058768707 := by
  apply lucas_primality 1022058768707 (2 : ZMod 1022058768707)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (26896283387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (26896283387, 1)] : List FactorBlock).map factorBlockValue).prod) = 1022058768707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_26896283387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1022058768707) ^ 511029384353 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1022058768707) ^ 53792566774 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1022058768707) ^ 38 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1171495867063 : Nat.Prime 1171495867063 := by
  apply lucas_primality 1171495867063 (5 : ZMod 1171495867063)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (127, 1), (1537396151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (127, 1), (1537396151, 1)] : List FactorBlock).map factorBlockValue).prod) = 1171495867063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_127
      · exact prime_oneHundredTwentyDN_1537396151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1171495867063) ^ 585747933531 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1171495867063) ^ 390498622354 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1171495867063) ^ 9224376906 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1171495867063) ^ 762 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1198375974329 : Nat.Prime 1198375974329 := by
  apply lucas_primality 1198375974329 (3 : ZMod 1198375974329)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (59, 1), (195302473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (59, 1), (195302473, 1)] : List FactorBlock).map factorBlockValue).prod) = 1198375974329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_59
      · exact prime_oneHundredTwentyDN_195302473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1198375974329) ^ 599187987164 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1198375974329) ^ 92182767256 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1198375974329) ^ 20311457192 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1198375974329) ^ 6136 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1538706810127 : Nat.Prime 1538706810127 := by
  apply lucas_primality 1538706810127 (3 : ZMod 1538706810127)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (79, 1), (613, 1), (278717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (79, 1), (613, 1), (278717, 1)] : List FactorBlock).map factorBlockValue).prod) = 1538706810127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_79
      · exact prime_oneHundredTwentyDN_613
      · exact prime_oneHundredTwentyDN_278717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1538706810127) ^ 769353405063 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1538706810127) ^ 512902270042 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1538706810127) ^ 80984568954 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1538706810127) ^ 19477301394 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1538706810127) ^ 2510125302 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1538706810127) ^ 5520678 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_2724679354157 : Nat.Prime 2724679354157 := by
  apply lucas_primality 2724679354157 (2 : ZMod 2724679354157)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (359, 1), (33589, 1), (56489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (359, 1), (33589, 1), (56489, 1)] : List FactorBlock).map factorBlockValue).prod) = 2724679354157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_359
      · exact prime_oneHundredTwentyDN_33589
      · exact prime_oneHundredTwentyDN_56489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2724679354157) ^ 1362339677078 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2724679354157) ^ 7589636084 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2724679354157) ^ 81118204 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2724679354157) ^ 48233804 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_4014078193691 : Nat.Prime 4014078193691 := by
  apply lucas_primality 4014078193691 (2 : ZMod 4014078193691)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (829, 1), (1051, 1), (460711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (829, 1), (1051, 1), (460711, 1)] : List FactorBlock).map factorBlockValue).prod) = 4014078193691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_829
      · exact prime_oneHundredTwentyDN_1051
      · exact prime_oneHundredTwentyDN_460711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4014078193691) ^ 2007039096845 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 802815638738 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 4842072610 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 3819294190 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 8712790 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_5260625686909 : Nat.Prime 5260625686909 := by
  apply lucas_primality 5260625686909 (6 : ZMod 5260625686909)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (151, 1), (947, 1), (340633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (151, 1), (947, 1), (340633, 1)] : List FactorBlock).map factorBlockValue).prod) = 5260625686909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_151
      · exact prime_oneHundredTwentyDN_947
      · exact prime_oneHundredTwentyDN_340633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5260625686909) ^ 2630312843454 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 5260625686909) ^ 1753541895636 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 5260625686909) ^ 34838580708 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 5260625686909) ^ 5555042964 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 5260625686909) ^ 15443676 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_5654278184189 : Nat.Prime 5654278184189 := by
  apply lucas_primality 5654278184189 (2 : ZMod 5654278184189)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (199, 1), (89916007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (199, 1), (89916007, 1)] : List FactorBlock).map factorBlockValue).prod) = 5654278184189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_79
      · exact prime_oneHundredTwentyDN_199
      · exact prime_oneHundredTwentyDN_89916007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5654278184189) ^ 2827139092094 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5654278184189) ^ 71573141572 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5654278184189) ^ 28413458212 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5654278184189) ^ 62884 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_6406133481313 : Nat.Prime 6406133481313 := by
  apply lucas_primality 6406133481313 (5 : ZMod 6406133481313)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (29, 1), (2301053693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (29, 1), (2301053693, 1)] : List FactorBlock).map factorBlockValue).prod) = 6406133481313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_29
      · exact prime_oneHundredTwentyDN_2301053693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6406133481313) ^ 3203066740656 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 6406133481313) ^ 2135377827104 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 6406133481313) ^ 220901154528 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 6406133481313) ^ 2784 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_8204421155869 : Nat.Prime 8204421155869 := by
  apply lucas_primality 8204421155869 (6 : ZMod 8204421155869)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (631, 2), (81769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (631, 2), (81769, 1)] : List FactorBlock).map factorBlockValue).prod) = 8204421155869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_631
      · exact prime_oneHundredTwentyDN_81769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8204421155869) ^ 4102210577934 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 8204421155869) ^ 2734807051956 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 8204421155869) ^ 1172060165124 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 8204421155869) ^ 13002252228 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 8204421155869) ^ 100336572 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_8450556055043 : Nat.Prime 8450556055043 := by
  apply lucas_primality 8450556055043 (2 : ZMod 8450556055043)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (83, 1), (2213346269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (83, 1), (2213346269, 1)] : List FactorBlock).map factorBlockValue).prod) = 8450556055043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_23
      · exact prime_oneHundredTwentyDN_83
      · exact prime_oneHundredTwentyDN_2213346269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8450556055043) ^ 4225278027521 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8450556055043) ^ 367415480654 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8450556055043) ^ 101813928374 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8450556055043) ^ 3818 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_8524454832463 : Nat.Prime 8524454832463 := by
  apply lucas_primality 8524454832463 (3 : ZMod 8524454832463)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (74775919583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (74775919583, 1)] : List FactorBlock).map factorBlockValue).prod) = 8524454832463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_74775919583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8524454832463) ^ 4262227416231 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 2841484944154 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 448655517498 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 114 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_9046635978727 : Nat.Prime 9046635978727 := by
  apply lucas_primality 9046635978727 (17 : ZMod 9046635978727)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1069, 1), (470150503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1069, 1), (470150503, 1)] : List FactorBlock).map factorBlockValue).prod) = 9046635978727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_1069
      · exact prime_oneHundredTwentyDN_470150503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 9046635978727) ^ 4523317989363 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 9046635978727) ^ 3015545326242 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 9046635978727) ^ 8462709054 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 9046635978727) ^ 19242 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_9566065542823 : Nat.Prime 9566065542823 := by
  apply lucas_primality 9566065542823 (5 : ZMod 9566065542823)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2347, 1), (679311571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2347, 1), (679311571, 1)] : List FactorBlock).map factorBlockValue).prod) = 9566065542823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_2347
      · exact prime_oneHundredTwentyDN_679311571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9566065542823) ^ 4783032771411 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 9566065542823) ^ 3188688514274 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 9566065542823) ^ 4075869426 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 9566065542823) ^ 14082 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_9785892628279 : Nat.Prime 9785892628279 := by
  apply lucas_primality 9785892628279 (6 : ZMod 9785892628279)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (229, 1), (20291147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (229, 1), (20291147, 1)] : List FactorBlock).map factorBlockValue).prod) = 9785892628279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_229
      · exact prime_oneHundredTwentyDN_20291147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9785892628279) ^ 4892946314139 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 3261964209426 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 752760971406 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 42733155582 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 482274 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_12908245282301 : Nat.Prime 12908245282301 := by
  apply lucas_primality 12908245282301 (3 : ZMod 12908245282301)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (3701, 1), (34877723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (3701, 1), (34877723, 1)] : List FactorBlock).map factorBlockValue).prod) = 12908245282301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_3701
      · exact prime_oneHundredTwentyDN_34877723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12908245282301) ^ 6454122641150 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 12908245282301) ^ 2581649056460 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 12908245282301) ^ 3487772300 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 12908245282301) ^ 370100 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_13971226936099 : Nat.Prime 13971226936099 := by
  apply lucas_primality 13971226936099 (2 : ZMod 13971226936099)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) = 13971226936099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_21617
      · exact prime_oneHundredTwentyDN_6336347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13971226936099) ^ 6985613468049 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 4657075645366 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 821836878594 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 646307394 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 2204934 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_15239370115789 : Nat.Prime 15239370115789 := by
  apply lucas_primality 15239370115789 (2 : ZMod 15239370115789)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (547, 1), (25512737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (547, 1), (25512737, 1)] : List FactorBlock).map factorBlockValue).prod) = 15239370115789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_547
      · exact prime_oneHundredTwentyDN_25512737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15239370115789) ^ 7619685057894 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 15239370115789) ^ 5079790038596 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 15239370115789) ^ 2177052873684 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 15239370115789) ^ 1172259239676 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 15239370115789) ^ 27859908804 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 15239370115789) ^ 597324 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_16162151074357 : Nat.Prime 16162151074357 := by
  apply lucas_primality 16162151074357 (2 : ZMod 16162151074357)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (31, 1), (886666177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (31, 1), (886666177, 1)] : List FactorBlock).map factorBlockValue).prod) = 16162151074357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_31
      · exact prime_oneHundredTwentyDN_886666177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16162151074357) ^ 8081075537178 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 16162151074357) ^ 5387383691452 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 16162151074357) ^ 2308878724908 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 16162151074357) ^ 521359712076 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 16162151074357) ^ 18228 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_18055173871829 : Nat.Prime 18055173871829 := by
  apply lucas_primality 18055173871829 (2 : ZMod 18055173871829)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (241, 1), (1101731381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (241, 1), (1101731381, 1)] : List FactorBlock).map factorBlockValue).prod) = 18055173871829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_241
      · exact prime_oneHundredTwentyDN_1101731381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18055173871829) ^ 9027586935914 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 18055173871829) ^ 1062069051284 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 18055173871829) ^ 74917733908 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 18055173871829) ^ 16388 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_19814936977403 : Nat.Prime 19814936977403 := by
  apply lucas_primality 19814936977403 (2 : ZMod 19814936977403)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2309, 1), (612972127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2309, 1), (612972127, 1)] : List FactorBlock).map factorBlockValue).prod) = 19814936977403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_2309
      · exact prime_oneHundredTwentyDN_612972127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19814936977403) ^ 9907468488701 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 19814936977403) ^ 2830705282486 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 19814936977403) ^ 8581609778 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 19814936977403) ^ 32326 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_23642614645087 : Nat.Prime 23642614645087 := by
  apply lucas_primality 23642614645087 (3 : ZMod 23642614645087)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (157, 1), (353497423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (157, 1), (353497423, 1)] : List FactorBlock).map factorBlockValue).prod) = 23642614645087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_71
      · exact prime_oneHundredTwentyDN_157
      · exact prime_oneHundredTwentyDN_353497423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23642614645087) ^ 11821307322543 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 23642614645087) ^ 7880871548362 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 23642614645087) ^ 332994572466 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 23642614645087) ^ 150589902198 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 23642614645087) ^ 66882 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_25866812093597 : Nat.Prime 25866812093597 := by
  apply lucas_primality 25866812093597 (2 : ZMod 25866812093597)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (541, 1), (11953240339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (541, 1), (11953240339, 1)] : List FactorBlock).map factorBlockValue).prod) = 25866812093597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_541
      · exact prime_oneHundredTwentyDN_11953240339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 25866812093597) ^ 12933406046798 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 25866812093597) ^ 47812961356 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 25866812093597) ^ 2164 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_30073867051861 : Nat.Prime 30073867051861 := by
  apply lucas_primality 30073867051861 (2 : ZMod 30073867051861)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (29, 1), (43, 1), (6337, 1), (21143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (29, 1), (43, 1), (6337, 1), (21143, 1)] : List FactorBlock).map factorBlockValue).prod) = 30073867051861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_29
      · exact prime_oneHundredTwentyDN_43
      · exact prime_oneHundredTwentyDN_6337
      · exact prime_oneHundredTwentyDN_21143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30073867051861) ^ 15036933525930 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 30073867051861) ^ 10024622350620 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 30073867051861) ^ 6014773410372 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 30073867051861) ^ 1037029898340 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 30073867051861) ^ 699392257020 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 30073867051861) ^ 4745757780 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 30073867051861) ^ 1422403020 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_30886550519203 : Nat.Prime 30886550519203 := by
  apply lucas_primality 30886550519203 (2 : ZMod 30886550519203)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 2), (193, 1), (5419, 1), (11161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 2), (193, 1), (5419, 1), (11161, 1)] : List FactorBlock).map factorBlockValue).prod) = 30886550519203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_193
      · exact prime_oneHundredTwentyDN_5419
      · exact prime_oneHundredTwentyDN_11161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30886550519203) ^ 15443275259601 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 30886550519203) ^ 10295516839734 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 30886550519203) ^ 4412364359886 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 30886550519203) ^ 160033940514 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 30886550519203) ^ 5699677158 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 30886550519203) ^ 2767364082 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_32500219188373 : Nat.Prime 32500219188373 := by
  apply lucas_primality 32500219188373 (2 : ZMod 32500219188373)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (17, 1), (83, 1), (3253, 1), (45389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (17, 1), (83, 1), (3253, 1), (45389, 1)] : List FactorBlock).map factorBlockValue).prod) = 32500219188373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_83
      · exact prime_oneHundredTwentyDN_3253
      · exact prime_oneHundredTwentyDN_45389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32500219188373) ^ 16250109594186 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 32500219188373) ^ 10833406396124 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 32500219188373) ^ 2500016860644 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 32500219188373) ^ 1911777599316 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 32500219188373) ^ 391568905884 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 32500219188373) ^ 9990845124 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 32500219188373) ^ 716037348 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_38009070719731 : Nat.Prime 38009070719731 := by
  apply lucas_primality 38009070719731 (2 : ZMod 38009070719731)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (11, 1), (367, 1), (34871027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (11, 1), (367, 1), (34871027, 1)] : List FactorBlock).map factorBlockValue).prod) = 38009070719731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_367
      · exact prime_oneHundredTwentyDN_34871027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38009070719731) ^ 19004535359865 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 38009070719731) ^ 12669690239910 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 38009070719731) ^ 7601814143946 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 38009070719731) ^ 3455370065430 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 38009070719731) ^ 103566950190 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 38009070719731) ^ 1089990 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_39629873954807 : Nat.Prime 39629873954807 := by
  apply lucas_primality 39629873954807 (5 : ZMod 39629873954807)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19814936977403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19814936977403, 1)] : List FactorBlock).map factorBlockValue).prod) = 39629873954807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_19814936977403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 39629873954807) ^ 19814936977403 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 39629873954807) ^ 2 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_41782361350123 : Nat.Prime 41782361350123 := by
  apply lucas_primality 41782361350123 (5 : ZMod 41782361350123)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (114269, 1), (20313841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (114269, 1), (20313841, 1)] : List FactorBlock).map factorBlockValue).prod) = 41782361350123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_114269
      · exact prime_oneHundredTwentyDN_20313841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 41782361350123) ^ 20891180675061 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 41782361350123) ^ 13927453783374 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 41782361350123) ^ 365649138 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 41782361350123) ^ 2056842 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_47
      · exact prime_oneHundredTwentyDN_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_47061672383657 : Nat.Prime 47061672383657 := by
  apply lucas_primality 47061672383657 (3 : ZMod 47061672383657)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (120055286693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (120055286693, 1)] : List FactorBlock).map factorBlockValue).prod) = 47061672383657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_120055286693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47061672383657) ^ 23530836191828 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 47061672383657) ^ 6723096054808 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 47061672383657) ^ 392 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_49146911386957 : Nat.Prime 49146911386957 := by
  apply lucas_primality 49146911386957 (5 : ZMod 49146911386957)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (59, 1), (127, 1), (197, 1), (54403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (59, 1), (127, 1), (197, 1), (54403, 1)] : List FactorBlock).map factorBlockValue).prod) = 49146911386957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_59
      · exact prime_oneHundredTwentyDN_127
      · exact prime_oneHundredTwentyDN_197
      · exact prime_oneHundredTwentyDN_54403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 49146911386957) ^ 24573455693478 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 49146911386957) ^ 16382303795652 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 49146911386957) ^ 2890994787468 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 49146911386957) ^ 832998498084 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 49146911386957) ^ 386983554228 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 49146911386957) ^ 249476707548 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 49146911386957) ^ 903386052 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_57793874370247 : Nat.Prime 57793874370247 := by
  apply lucas_primality 57793874370247 (5 : ZMod 57793874370247)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17, 1), (96697, 1), (279029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17, 1), (96697, 1), (279029, 1)] : List FactorBlock).map factorBlockValue).prod) = 57793874370247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_96697
      · exact prime_oneHundredTwentyDN_279029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 57793874370247) ^ 28896937185123 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 19264624790082 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 8256267767178 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 3399639668838 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 597680118 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 207124974 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_60516180717823 : Nat.Prime 60516180717823 := by
  apply lucas_primality 60516180717823 (3 : ZMod 60516180717823)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (149, 1), (7521275257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (149, 1), (7521275257, 1)] : List FactorBlock).map factorBlockValue).prod) = 60516180717823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_149
      · exact prime_oneHundredTwentyDN_7521275257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 60516180717823) ^ 30258090358911 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 60516180717823) ^ 20172060239274 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 60516180717823) ^ 406148863878 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 60516180717823) ^ 8046 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_61638694796963 : Nat.Prime 61638694796963 := by
  apply lucas_primality 61638694796963 (2 : ZMod 61638694796963)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (43, 1), (349, 1), (3637, 1), (19471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (43, 1), (349, 1), (3637, 1), (19471, 1)] : List FactorBlock).map factorBlockValue).prod) = 61638694796963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_29
      · exact prime_oneHundredTwentyDN_43
      · exact prime_oneHundredTwentyDN_349
      · exact prime_oneHundredTwentyDN_3637
      · exact prime_oneHundredTwentyDN_19471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 61638694796963) ^ 30819347398481 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 61638694796963) ^ 2125472234378 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 61638694796963) ^ 1433458018534 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 61638694796963) ^ 176615171338 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 61638694796963) ^ 16947675226 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 61638694796963) ^ 3165666622 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_67572436011161 : Nat.Prime 67572436011161 := by
  apply lucas_primality 67572436011161 (3 : ZMod 67572436011161)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (31, 1), (331, 1), (4937, 1), (33347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (31, 1), (331, 1), (4937, 1), (33347, 1)] : List FactorBlock).map factorBlockValue).prod) = 67572436011161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_31
      · exact prime_oneHundredTwentyDN_331
      · exact prime_oneHundredTwentyDN_4937
      · exact prime_oneHundredTwentyDN_33347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 67572436011161) ^ 33786218005580 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 67572436011161) ^ 13514487202232 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 67572436011161) ^ 2179756000360 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 67572436011161) ^ 204146332360 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 67572436011161) ^ 13686942680 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 67572436011161) ^ 2026342280 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_100257985466497 : Nat.Prime 100257985466497 := by
  apply lucas_primality 100257985466497 (5 : ZMod 100257985466497)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) = 100257985466497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_173
      · exact prime_oneHundredTwentyDN_185153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 100257985466497) ^ 50128992733248 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 33419328488832 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 9114362315136 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 7712152728192 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 5276736077184 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 579525927552 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 541487232 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_129164626112089 : Nat.Prime 129164626112089 := by
  apply lucas_primality 129164626112089 (38 : ZMod 129164626112089)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (17, 1), (45225709423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (17, 1), (45225709423, 1)] : List FactorBlock).map factorBlockValue).prod) = 129164626112089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_45225709423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (38 : ZMod 129164626112089) ^ 64582313056044 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (38 : ZMod 129164626112089) ^ 43054875370696 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (38 : ZMod 129164626112089) ^ 18452089444584 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (38 : ZMod 129164626112089) ^ 7597919183064 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (38 : ZMod 129164626112089) ^ 2856 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_130417135331503 : Nat.Prime 130417135331503 := by
  apply lucas_primality 130417135331503 (3 : ZMod 130417135331503)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (749523766273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (749523766273, 1)] : List FactorBlock).map factorBlockValue).prod) = 130417135331503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_29
      · exact prime_oneHundredTwentyDN_749523766273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 130417135331503) ^ 65208567665751 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 43472378443834 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 4497142597638 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 174 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_139034446677491 : Nat.Prime 139034446677491 := by
  apply lucas_primality 139034446677491 (2 : ZMod 139034446677491)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (19, 1), (443, 1), (18151967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (19, 1), (443, 1), (18151967, 1)] : List FactorBlock).map factorBlockValue).prod) = 139034446677491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_443
      · exact prime_oneHundredTwentyDN_18151967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 139034446677491) ^ 69517223338745 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 27806889335498 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 19862063811070 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 10694957436730 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 7317602456710 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 313847509430 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 7659470 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_144730980259499 : Nat.Prime 144730980259499 := by
  apply lucas_primality 144730980259499 (2 : ZMod 144730980259499)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (28097, 1), (17285633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (28097, 1), (17285633, 1)] : List FactorBlock).map factorBlockValue).prod) = 144730980259499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_149
      · exact prime_oneHundredTwentyDN_28097
      · exact prime_oneHundredTwentyDN_17285633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 144730980259499) ^ 72365490129749 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 144730980259499) ^ 971348860802 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 144730980259499) ^ 5151118634 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 144730980259499) ^ 8372906 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_149740879250467 : Nat.Prime 149740879250467 := by
  apply lucas_primality 149740879250467 (17 : ZMod 149740879250467)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 2), (56591413171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 2), (56591413171, 1)] : List FactorBlock).map factorBlockValue).prod) = 149740879250467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_56591413171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 149740879250467) ^ 74870439625233 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 149740879250467) ^ 49913626416822 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 149740879250467) ^ 21391554178638 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 149740879250467) ^ 2646 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_194874783926681 : Nat.Prime 194874783926681 := by
  apply lucas_primality 194874783926681 (3 : ZMod 194874783926681)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (13, 1), (47, 1), (17351, 1), (41777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (13, 1), (47, 1), (17351, 1), (41777, 1)] : List FactorBlock).map factorBlockValue).prod) = 194874783926681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_47
      · exact prime_oneHundredTwentyDN_17351
      · exact prime_oneHundredTwentyDN_41777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 194874783926681) ^ 97437391963340 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 38974956785336 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 17715889447880 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 14990367994360 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 4146271998440 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 11231328680 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 4664642840 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_197320078064177 : Nat.Prime 197320078064177 := by
  apply lucas_primality 197320078064177 (3 : ZMod 197320078064177)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1327, 1), (4273, 1), (2174941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1327, 1), (4273, 1), (2174941, 1)] : List FactorBlock).map factorBlockValue).prod) = 197320078064177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_1327
      · exact prime_oneHundredTwentyDN_4273
      · exact prime_oneHundredTwentyDN_2174941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 197320078064177) ^ 98660039032088 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 197320078064177) ^ 148696366288 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 197320078064177) ^ 46178347312 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 197320078064177) ^ 90724336 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_217308140689699 : Nat.Prime 217308140689699 := by
  apply lucas_primality 217308140689699 (3 : ZMod 217308140689699)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (137, 1), (8753, 1), (3355867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (137, 1), (8753, 1), (3355867, 1)] : List FactorBlock).map factorBlockValue).prod) = 217308140689699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_137
      · exact prime_oneHundredTwentyDN_8753
      · exact prime_oneHundredTwentyDN_3355867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 217308140689699) ^ 108654070344849 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 217308140689699) ^ 72436046896566 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 217308140689699) ^ 1586190807954 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 217308140689699) ^ 24826704066 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 217308140689699) ^ 64754694 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_234523392557819 : Nat.Prime 234523392557819 := by
  apply lucas_primality 234523392557819 (2 : ZMod 234523392557819)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (67, 1), (137, 1), (8431, 1), (16651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (67, 1), (137, 1), (8431, 1), (16651, 1)] : List FactorBlock).map factorBlockValue).prod) = 234523392557819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_67
      · exact prime_oneHundredTwentyDN_137
      · exact prime_oneHundredTwentyDN_8431
      · exact prime_oneHundredTwentyDN_16651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 234523392557819) ^ 117261696278909 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 234523392557819) ^ 33503341793974 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 234523392557819) ^ 18040260965986 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 234523392557819) ^ 3500349142654 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 234523392557819) ^ 1711849580714 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 234523392557819) ^ 27816794278 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 234523392557819) ^ 14084643118 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_240844691621461 : Nat.Prime 240844691621461 := by
  apply lucas_primality 240844691621461 (2 : ZMod 240844691621461)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (4014078193691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (4014078193691, 1)] : List FactorBlock).map factorBlockValue).prod) = 240844691621461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_4014078193691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 240844691621461) ^ 120422345810730 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 80281563873820 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 48168938324292 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 60 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_255709017924433 : Nat.Prime 255709017924433 := by
  apply lucas_primality 255709017924433 (5 : ZMod 255709017924433)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (677, 1), (9043, 1), (870169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (677, 1), (9043, 1), (870169, 1)] : List FactorBlock).map factorBlockValue).prod) = 255709017924433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_677
      · exact prime_oneHundredTwentyDN_9043
      · exact prime_oneHundredTwentyDN_870169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 255709017924433) ^ 127854508962216 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 255709017924433) ^ 85236339308144 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 255709017924433) ^ 377709036816 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 255709017924433) ^ 28277011824 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 255709017924433) ^ 293861328 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_10789
      · exact prime_oneHundredTwentyDN_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_273308408322643 : Nat.Prime 273308408322643 := by
  apply lucas_primality 273308408322643 (3 : ZMod 273308408322643)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (1109, 1), (5273, 1), (33721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (1109, 1), (5273, 1), (33721, 1)] : List FactorBlock).map factorBlockValue).prod) = 273308408322643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_1109
      · exact prime_oneHundredTwentyDN_5273
      · exact prime_oneHundredTwentyDN_33721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 273308408322643) ^ 136654204161321 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 91102802774214 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 39044058331806 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 24846218938422 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 246445814538 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 51831672354 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 8104991202 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_281546073328321 : Nat.Prime 281546073328321 := by
  apply lucas_primality 281546073328321 (17 : ZMod 281546073328321)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 1), (797, 1), (122658787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 1), (797, 1), (122658787, 1)] : List FactorBlock).map factorBlockValue).prod) = 281546073328321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_797
      · exact prime_oneHundredTwentyDN_122658787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 281546073328321) ^ 140773036664160 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 281546073328321) ^ 93848691109440 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 281546073328321) ^ 56309214665664 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 281546073328321) ^ 353257306560 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 281546073328321) ^ 2295360 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_383611913911283 : Nat.Prime 383611913911283 := by
  apply lucas_primality 383611913911283 (2 : ZMod 383611913911283)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (787, 1), (9739, 1), (72959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (787, 1), (9739, 1), (72959, 1)] : List FactorBlock).map factorBlockValue).prod) = 383611913911283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_787
      · exact prime_oneHundredTwentyDN_9739
      · exact prime_oneHundredTwentyDN_72959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 383611913911283) ^ 191805956955641 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 383611913911283) ^ 54801701987326 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 383611913911283) ^ 487435722886 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 383611913911283) ^ 39389250838 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 383611913911283) ^ 5257910798 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_466718517702823 : Nat.Prime 466718517702823 := by
  apply lucas_primality 466718517702823 (3 : ZMod 466718517702823)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (23057, 1), (43813733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (23057, 1), (43813733, 1)] : List FactorBlock).map factorBlockValue).prod) = 466718517702823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_23057
      · exact prime_oneHundredTwentyDN_43813733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 466718517702823) ^ 233359258851411 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 466718517702823) ^ 155572839234274 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 466718517702823) ^ 66674073957546 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 466718517702823) ^ 42428956154802 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 466718517702823) ^ 20241944646 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 466718517702823) ^ 10652334 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_487995060087097 : Nat.Prime 487995060087097 := by
  apply lucas_primality 487995060087097 (5 : ZMod 487995060087097)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2591, 1), (7847598419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2591, 1), (7847598419, 1)] : List FactorBlock).map factorBlockValue).prod) = 487995060087097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_2591
      · exact prime_oneHundredTwentyDN_7847598419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 487995060087097) ^ 243997530043548 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 487995060087097) ^ 162665020029032 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 487995060087097) ^ 188342362056 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 487995060087097) ^ 62184 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_767223827822567 : Nat.Prime 767223827822567 := by
  apply lucas_primality 767223827822567 (5 : ZMod 767223827822567)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (383611913911283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (383611913911283, 1)] : List FactorBlock).map factorBlockValue).prod) = 767223827822567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_383611913911283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 767223827822567) ^ 383611913911283 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 767223827822567) ^ 2 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_813016227818633 : Nat.Prime 813016227818633 := by
  apply lucas_primality 813016227818633 (5 : ZMod 813016227818633)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (950531, 1), (5627161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (950531, 1), (5627161, 1)] : List FactorBlock).map factorBlockValue).prod) = 813016227818633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_950531
      · exact prime_oneHundredTwentyDN_5627161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 813016227818633) ^ 406508113909316 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 813016227818633) ^ 42790327779928 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 813016227818633) ^ 855328472 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 813016227818633) ^ 144480712 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1200138209940499 : Nat.Prime 1200138209940499 := by
  apply lucas_primality 1200138209940499 (2 : ZMod 1200138209940499)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (230551, 1), (37721171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (230551, 1), (37721171, 1)] : List FactorBlock).map factorBlockValue).prod) = 1200138209940499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_23
      · exact prime_oneHundredTwentyDN_230551
      · exact prime_oneHundredTwentyDN_37721171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1200138209940499) ^ 600069104970249 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1200138209940499) ^ 400046069980166 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1200138209940499) ^ 52179922171326 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1200138209940499) ^ 5205521598 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1200138209940499) ^ 31816038 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1291737826932829 : Nat.Prime 1291737826932829 := by
  apply lucas_primality 1291737826932829 (2 : ZMod 1291737826932829)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (9785892628279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (9785892628279, 1)] : List FactorBlock).map factorBlockValue).prod) = 1291737826932829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_9785892628279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1291737826932829) ^ 645868913466414 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 430579275644276 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 117430711539348 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 132 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1769293600347029 : Nat.Prime 1769293600347029 := by
  apply lucas_primality 1769293600347029 (2 : ZMod 1769293600347029)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (367, 1), (172177267453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (367, 1), (172177267453, 1)] : List FactorBlock).map factorBlockValue).prod) = 1769293600347029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_367
      · exact prime_oneHundredTwentyDN_172177267453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1769293600347029) ^ 884646800173514 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769293600347029) ^ 252756228621004 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769293600347029) ^ 4820963488684 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769293600347029) ^ 10276 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_4389020540633171 : Nat.Prime 4389020540633171 := by
  apply lucas_primality 4389020540633171 (7 : ZMod 4389020540633171)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (13327, 1), (2533330567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (13327, 1), (2533330567, 1)] : List FactorBlock).map factorBlockValue).prod) = 4389020540633171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_13327
      · exact prime_oneHundredTwentyDN_2533330567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4389020540633171) ^ 2194510270316585 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4389020540633171) ^ 877804108126634 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4389020540633171) ^ 337616964664090 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4389020540633171) ^ 329332973710 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4389020540633171) ^ 1732510 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_5066744382093707 : Nat.Prime 5066744382093707 := by
  apply lucas_primality 5066744382093707 (2 : ZMod 5066744382093707)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (194874783926681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (194874783926681, 1)] : List FactorBlock).map factorBlockValue).prod) = 5066744382093707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_194874783926681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5066744382093707) ^ 2533372191046853 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5066744382093707) ^ 389749567853362 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5066744382093707) ^ 26 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_8151940739207033 : Nat.Prime 8151940739207033 := by
  apply lucas_primality 8151940739207033 (3 : ZMod 8151940739207033)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (997, 1), (1022058768707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (997, 1), (1022058768707, 1)] : List FactorBlock).map factorBlockValue).prod) = 8151940739207033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_997
      · exact prime_oneHundredTwentyDN_1022058768707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8151940739207033) ^ 4075970369603516 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8151940739207033) ^ 8176470149656 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8151940739207033) ^ 7976 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_29580241950103007 : Nat.Prime 29580241950103007 := by
  apply lucas_primality 29580241950103007 (5 : ZMod 29580241950103007)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (479, 1), (91541, 1), (337303277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (479, 1), (91541, 1), (337303277, 1)] : List FactorBlock).map factorBlockValue).prod) = 29580241950103007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_479
      · exact prime_oneHundredTwentyDN_91541
      · exact prime_oneHundredTwentyDN_337303277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 29580241950103007) ^ 14790120975051503 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 29580241950103007) ^ 61754158559714 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 29580241950103007) ^ 323136539366 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 29580241950103007) ^ 87696278 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_37051420944511243 : Nat.Prime 37051420944511243 := by
  apply lucas_primality 37051420944511243 (3 : ZMod 37051420944511243)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) = 37051420944511243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_131
      · exact prime_oneHundredTwentyDN_170603
      · exact prime_oneHundredTwentyDN_92103133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37051420944511243) ^ 18525710472255621 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 12350473648170414 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 282835274385582 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 217179187614 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 402281874 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_53015135238325067 : Nat.Prime 53015135238325067 := by
  apply lucas_primality 53015135238325067 (2 : ZMod 53015135238325067)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (163, 1), (9566065542823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (163, 1), (9566065542823, 1)] : List FactorBlock).map factorBlockValue).prod) = 53015135238325067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_163
      · exact prime_oneHundredTwentyDN_9566065542823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53015135238325067) ^ 26507567619162533 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 53015135238325067) ^ 3118537366960298 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 53015135238325067) ^ 325246228455982 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 53015135238325067) ^ 5542 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_54505364198768423 : Nat.Prime 54505364198768423 := by
  apply lucas_primality 54505364198768423 (5 : ZMod 54505364198768423)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (139, 1), (8524454832463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (139, 1), (8524454832463, 1)] : List FactorBlock).map factorBlockValue).prod) = 54505364198768423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_23
      · exact prime_oneHundredTwentyDN_139
      · exact prime_oneHundredTwentyDN_8524454832463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 54505364198768423) ^ 27252682099384211 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 2369798443424714 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 392124922293298 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 6394 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_70075919093336591 : Nat.Prime 70075919093336591 := by
  apply lucas_primality 70075919093336591 (14 : ZMod 70075919093336591)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) = 70075919093336591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_31
      · exact prime_oneHundredTwentyDN_24841
      · exact prime_oneHundredTwentyDN_1299989947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 70075919093336591) ^ 35037959546668295 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 14015183818667318 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 10010845584762370 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2260513519139890 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2820978184990 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 53904970 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_118386907891554073 : Nat.Prime 118386907891554073 := by
  apply lucas_primality 118386907891554073 (5 : ZMod 118386907891554073)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (73, 1), (67572436011161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (73, 1), (67572436011161, 1)] : List FactorBlock).map factorBlockValue).prod) = 118386907891554073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_73
      · exact prime_oneHundredTwentyDN_67572436011161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 118386907891554073) ^ 59193453945777036 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 118386907891554073) ^ 39462302630518024 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 118386907891554073) ^ 1621738464267864 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 118386907891554073) ^ 1752 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_136916689374571747 : Nat.Prime 136916689374571747 := by
  apply lucas_primality 136916689374571747 (2 : ZMod 136916689374571747)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113, 1), (22453, 1), (49433, 1), (181943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113, 1), (22453, 1), (49433, 1), (181943, 1)] : List FactorBlock).map factorBlockValue).prod) = 136916689374571747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_113
      · exact prime_oneHundredTwentyDN_22453
      · exact prime_oneHundredTwentyDN_49433
      · exact prime_oneHundredTwentyDN_181943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 136916689374571747) ^ 68458344687285873 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 136916689374571747) ^ 45638896458190582 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 136916689374571747) ^ 1211652118359042 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 136916689374571747) ^ 6097924080282 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 136916689374571747) ^ 2769742669362 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 136916689374571747) ^ 752525183022 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_139271123883117227 : Nat.Prime 139271123883117227 := by
  apply lucas_primality 139271123883117227 (2 : ZMod 139271123883117227)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (13, 1), (227, 1), (313, 1), (877, 1), (1116419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (13, 1), (227, 1), (313, 1), (877, 1), (1116419, 1)] : List FactorBlock).map factorBlockValue).prod) = 139271123883117227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_227
      · exact prime_oneHundredTwentyDN_313
      · exact prime_oneHundredTwentyDN_877
      · exact prime_oneHundredTwentyDN_1116419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 139271123883117227) ^ 69635561941558613 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 139271123883117227) ^ 19895874840445318 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 139271123883117227) ^ 12661011262101566 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 139271123883117227) ^ 10713163375624402 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 139271123883117227) ^ 613529180101838 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 139271123883117227) ^ 444955667358202 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 139271123883117227) ^ 158804018110738 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 139271123883117227) ^ 124748077454 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_166002379433901781 : Nat.Prime 166002379433901781 := by
  apply lucas_primality 166002379433901781 (6 : ZMod 166002379433901781)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (61, 3), (67, 1), (151, 1), (15647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (61, 3), (67, 1), (151, 1), (15647, 1)] : List FactorBlock).map factorBlockValue).prod) = 166002379433901781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_61
      · exact prime_oneHundredTwentyDN_67
      · exact prime_oneHundredTwentyDN_151
      · exact prime_oneHundredTwentyDN_15647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 166002379433901781) ^ 83001189716950890 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 166002379433901781) ^ 55334126477967260 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 166002379433901781) ^ 33200475886780356 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 166002379433901781) ^ 23714625633414540 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 166002379433901781) ^ 15091125403081980 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 166002379433901781) ^ 2721350482522980 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 166002379433901781) ^ 2477647454237340 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 166002379433901781) ^ 1099353506184780 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 166002379433901781) ^ 10609214509740 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_185560283253726743 : Nat.Prime 185560283253726743 := by
  apply lucas_primality 185560283253726743 (5 : ZMod 185560283253726743)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2441, 1), (38009070719731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2441, 1), (38009070719731, 1)] : List FactorBlock).map factorBlockValue).prod) = 185560283253726743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_2441
      · exact prime_oneHundredTwentyDN_38009070719731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 185560283253726743) ^ 92780141626863371 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 185560283253726743) ^ 76018141439462 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 185560283253726743) ^ 4882 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_445131170801101231 : Nat.Prime 445131170801101231 := by
  apply lucas_primality 445131170801101231 (3 : ZMod 445131170801101231)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1033, 1), (1431847, 1), (10031591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1033, 1), (1431847, 1), (10031591, 1)] : List FactorBlock).map factorBlockValue).prod) = 445131170801101231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_1033
      · exact prime_oneHundredTwentyDN_1431847
      · exact prime_oneHundredTwentyDN_10031591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 445131170801101231) ^ 222565585400550615 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 445131170801101231) ^ 148377056933700410 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 445131170801101231) ^ 89026234160220246 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 445131170801101231) ^ 430911104357310 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 445131170801101231) ^ 310879005090 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 445131170801101231) ^ 44372938530 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1129558801352365613 : Nat.Prime 1129558801352365613 := by
  apply lucas_primality 1129558801352365613 (2 : ZMod 1129558801352365613)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (229, 1), (8105401, 1), (152138407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (229, 1), (8105401, 1), (152138407, 1)] : List FactorBlock).map factorBlockValue).prod) = 1129558801352365613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_229
      · exact prime_oneHundredTwentyDN_8105401
      · exact prime_oneHundredTwentyDN_152138407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1129558801352365613) ^ 564779400676182806 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1129558801352365613) ^ 4932571184944828 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1129558801352365613) ^ 139358780812 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1129558801352365613) ^ 7424547316 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1492065108799822793 : Nat.Prime 1492065108799822793 := by
  apply lucas_primality 1492065108799822793 (3 : ZMod 1492065108799822793)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (47981, 1), (88873, 1), (1901651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (47981, 1), (88873, 1), (1901651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1492065108799822793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_23
      · exact prime_oneHundredTwentyDN_47981
      · exact prime_oneHundredTwentyDN_88873
      · exact prime_oneHundredTwentyDN_1901651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1492065108799822793) ^ 746032554399911396 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 64872396034774904 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 31096998995432 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 16788733460104 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 784615635992 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_2146498216888109467 : Nat.Prime 2146498216888109467 := by
  apply lucas_primality 2146498216888109467 (2 : ZMod 2146498216888109467)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59183, 1), (656749, 1), (9204133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59183, 1), (656749, 1), (9204133, 1)] : List FactorBlock).map factorBlockValue).prod) = 2146498216888109467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_59183
      · exact prime_oneHundredTwentyDN_656749
      · exact prime_oneHundredTwentyDN_9204133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2146498216888109467) ^ 1073249108444054733 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2146498216888109467) ^ 715499405629369822 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2146498216888109467) ^ 36268830861702 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2146498216888109467) ^ 3268369220034 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2146498216888109467) ^ 233210256402 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_101
      · exact prime_oneHundredTwentyDN_191
      · exact prime_oneHundredTwentyDN_48017
      · exact prime_oneHundredTwentyDN_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_2346064108363272911 : Nat.Prime 2346064108363272911 := by
  apply lucas_primality 2346064108363272911 (17 : ZMod 2346064108363272911)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (25933, 1), (9046635978727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (25933, 1), (9046635978727, 1)] : List FactorBlock).map factorBlockValue).prod) = 2346064108363272911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_25933
      · exact prime_oneHundredTwentyDN_9046635978727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 2346064108363272911) ^ 1173032054181636455 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 2346064108363272911) ^ 469212821672654582 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 2346064108363272911) ^ 90466359787270 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (17 : ZMod 2346064108363272911) ^ 259330 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_2356980392894937077 : Nat.Prime 2356980392894937077 := by
  apply lucas_primality 2356980392894937077 (2 : ZMod 2356980392894937077)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1487, 1), (125183, 1), (3165480589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1487, 1), (125183, 1), (3165480589, 1)] : List FactorBlock).map factorBlockValue).prod) = 2356980392894937077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_1487
      · exact prime_oneHundredTwentyDN_125183
      · exact prime_oneHundredTwentyDN_3165480589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2356980392894937077) ^ 1178490196447468538 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2356980392894937077) ^ 1585057426291148 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2356980392894937077) ^ 18828278543372 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2356980392894937077) ^ 744588484 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_2418504985635183013 : Nat.Prime 2418504985635183013 := by
  apply lucas_primality 2418504985635183013 (2 : ZMod 2418504985635183013)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (43, 1), (6277, 1), (132257, 1), (182123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (43, 1), (6277, 1), (132257, 1), (182123, 1)] : List FactorBlock).map factorBlockValue).prod) = 2418504985635183013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_31
      · exact prime_oneHundredTwentyDN_43
      · exact prime_oneHundredTwentyDN_6277
      · exact prime_oneHundredTwentyDN_132257
      · exact prime_oneHundredTwentyDN_182123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2418504985635183013) ^ 1209252492817591506 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2418504985635183013) ^ 806168328545061004 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2418504985635183013) ^ 78016289859199452 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2418504985635183013) ^ 56244301991515884 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2418504985635183013) ^ 385296317609556 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2418504985635183013) ^ 18286404391716 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2418504985635183013) ^ 13279514315244 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_3165334654942473973 : Nat.Prime 3165334654942473973 := by
  apply lucas_primality 3165334654942473973 (2 : ZMod 3165334654942473973)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (179, 1), (30073867051861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (179, 1), (30073867051861, 1)] : List FactorBlock).map factorBlockValue).prod) = 3165334654942473973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_179
      · exact prime_oneHundredTwentyDN_30073867051861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3165334654942473973) ^ 1582667327471236986 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3165334654942473973) ^ 1055111551647491324 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3165334654942473973) ^ 452190664991781996 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3165334654942473973) ^ 17683433826494268 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3165334654942473973) ^ 105252 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_3503795954666829551 : Nat.Prime 3503795954666829551 := by
  apply lucas_primality 3503795954666829551 (13 : ZMod 3503795954666829551)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) = 3503795954666829551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_70075919093336591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 3503795954666829551) ^ 1751897977333414775 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 700759190933365910 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 50 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_4527184655447032079 : Nat.Prime 4527184655447032079 := by
  apply lucas_primality 4527184655447032079 (7 : ZMod 4527184655447032079)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (5821, 1), (152597, 1), (110796689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (5821, 1), (152597, 1), (110796689, 1)] : List FactorBlock).map factorBlockValue).prod) = 4527184655447032079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_23
      · exact prime_oneHundredTwentyDN_5821
      · exact prime_oneHundredTwentyDN_152597
      · exact prime_oneHundredTwentyDN_110796689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4527184655447032079) ^ 2263592327723516039 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 196834115454218786 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 777733148161318 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 29667586226774 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 40860288302 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_5695027857389254597 : Nat.Prime 5695027857389254597 := by
  apply lucas_primality 5695027857389254597 (2 : ZMod 5695027857389254597)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1087, 1), (14891, 1), (29319813199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1087, 1), (14891, 1), (29319813199, 1)] : List FactorBlock).map factorBlockValue).prod) = 5695027857389254597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_1087
      · exact prime_oneHundredTwentyDN_14891
      · exact prime_oneHundredTwentyDN_29319813199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5695027857389254597) ^ 2847513928694627298 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5695027857389254597) ^ 1898342619129751532 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5695027857389254597) ^ 5239216060155708 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5695027857389254597) ^ 382447643367756 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5695027857389254597) ^ 194238204 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_6140693439609514343 : Nat.Prime 6140693439609514343 := by
  apply lucas_primality 6140693439609514343 (5 : ZMod 6140693439609514343)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (199, 1), (217308140689699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (199, 1), (217308140689699, 1)] : List FactorBlock).map factorBlockValue).prod) = 6140693439609514343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_71
      · exact prime_oneHundredTwentyDN_199
      · exact prime_oneHundredTwentyDN_217308140689699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6140693439609514343) ^ 3070346719804757171 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 6140693439609514343) ^ 86488639994500202 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 6140693439609514343) ^ 30857755977937258 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 6140693439609514343) ^ 28258 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_11398275728545548041 : Nat.Prime 11398275728545548041 := by
  apply lucas_primality 11398275728545548041 (3 : ZMod 11398275728545548041)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (173, 1), (149740879250467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (173, 1), (149740879250467, 1)] : List FactorBlock).map factorBlockValue).prod) = 11398275728545548041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_173
      · exact prime_oneHundredTwentyDN_149740879250467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11398275728545548041) ^ 5699137864272774020 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11398275728545548041) ^ 2279655145709109608 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11398275728545548041) ^ 1036206884413231640 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11398275728545548041) ^ 65885986870205480 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11398275728545548041) ^ 76120 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_13311937837557174217 : Nat.Prime 13311937837557174217 := by
  apply lucas_primality 13311937837557174217 (5 : ZMod 13311937837557174217)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4253, 1), (130417135331503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4253, 1), (130417135331503, 1)] : List FactorBlock).map factorBlockValue).prod) = 13311937837557174217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_4253
      · exact prime_oneHundredTwentyDN_130417135331503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 13311937837557174217) ^ 6655968918778587108 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 4437312612519058072 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 3130011247956072 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 102072 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_34186284054161410879 : Nat.Prime 34186284054161410879 := by
  apply lucas_primality 34186284054161410879 (3 : ZMod 34186284054161410879)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (1223, 1), (13311367, 1), (16666033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (1223, 1), (13311367, 1), (16666033, 1)] : List FactorBlock).map factorBlockValue).prod) = 34186284054161410879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_1223
      · exact prime_oneHundredTwentyDN_13311367
      · exact prime_oneHundredTwentyDN_16666033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34186284054161410879) ^ 17093142027080705439 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 34186284054161410879) ^ 11395428018053803626 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 34186284054161410879) ^ 4883754864880201554 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 34186284054161410879) ^ 27952807893835986 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 34186284054161410879) ^ 2568202353234 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 34186284054161410879) ^ 2051255031966 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_36265159998777480317 : Nat.Prime 36265159998777480317 := by
  apply lucas_primality 36265159998777480317 (5 : ZMod 36265159998777480317)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (29, 1), (73, 1), (47061672383657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (29, 1), (73, 1), (47061672383657, 1)] : List FactorBlock).map factorBlockValue).prod) = 36265159998777480317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_29
      · exact prime_oneHundredTwentyDN_73
      · exact prime_oneHundredTwentyDN_47061672383657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36265159998777480317) ^ 18132579999388740158 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 5180737142682497188 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 2789627692213652332 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 1250522758578533804 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 496783013681883292 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 770588 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_52983531609217552957 : Nat.Prime 52983531609217552957 := by
  apply lucas_primality 52983531609217552957 (5 : ZMod 52983531609217552957)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) = 52983531609217552957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_2063
      · exact prime_oneHundredTwentyDN_15269
      · exact prime_oneHundredTwentyDN_140168308879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52983531609217552957) ^ 26491765804608776478 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 17661177203072517652 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 25682758899281412 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 3470006654608524 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 377999364 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_58618659408858889003 : Nat.Prime 58618659408858889003 := by
  apply lucas_primality 58618659408858889003 (2 : ZMod 58618659408858889003)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (149, 1), (43063, 1), (39041767819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (149, 1), (43063, 1), (39041767819, 1)] : List FactorBlock).map factorBlockValue).prod) = 58618659408858889003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_149
      · exact prime_oneHundredTwentyDN_43063
      · exact prime_oneHundredTwentyDN_39041767819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 58618659408858889003) ^ 29309329704429444501 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 58618659408858889003) ^ 19539553136286296334 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 58618659408858889003) ^ 4509127646835299154 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 58618659408858889003) ^ 393413821535965698 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 58618659408858889003) ^ 1361230276777254 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 58618659408858889003) ^ 1501434558 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_64058555872321487129 : Nat.Prime 64058555872321487129 := by
  apply lucas_primality 64058555872321487129 (3 : ZMod 64058555872321487129)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (307, 1), (431, 1), (60516180717823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (307, 1), (431, 1), (60516180717823, 1)] : List FactorBlock).map factorBlockValue).prod) = 64058555872321487129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_307
      · exact prime_oneHundredTwentyDN_431
      · exact prime_oneHundredTwentyDN_60516180717823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 64058555872321487129) ^ 32029277936160743564 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 64058555872321487129) ^ 208659791115053704 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 64058555872321487129) ^ 148627739842973288 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 64058555872321487129) ^ 1058536 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_93983219589341321849 : Nat.Prime 93983219589341321849 := by
  apply lucas_primality 93983219589341321849 (3 : ZMod 93983219589341321849)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (204557, 1), (8204421155869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (204557, 1), (8204421155869, 1)] : List FactorBlock).map factorBlockValue).prod) = 93983219589341321849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_204557
      · exact prime_oneHundredTwentyDN_8204421155869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 93983219589341321849) ^ 46991609794670660924 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 93983219589341321849) ^ 13426174227048760264 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 93983219589341321849) ^ 459447584728664 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 93983219589341321849) ^ 11455192 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_121531344317416447031 : Nat.Prime 121531344317416447031 := by
  apply lucas_primality 121531344317416447031 (7 : ZMod 121531344317416447031)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1877, 1), (14198059, 1), (456031721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1877, 1), (14198059, 1), (456031721, 1)] : List FactorBlock).map factorBlockValue).prod) = 121531344317416447031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_1877
      · exact prime_oneHundredTwentyDN_14198059
      · exact prime_oneHundredTwentyDN_456031721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 121531344317416447031) ^ 60765672158708223515 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 121531344317416447031) ^ 24306268863483289406 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 121531344317416447031) ^ 64747652806295390 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 121531344317416447031) ^ 8559715403170 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 121531344317416447031) ^ 266497567430 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_150811814764477236133 : Nat.Prime 150811814764477236133 := by
  apply lucas_primality 150811814764477236133 (2 : ZMod 150811814764477236133)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (173, 1), (9221, 1), (60607, 1), (6189961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (173, 1), (9221, 1), (60607, 1), (6189961, 1)] : List FactorBlock).map factorBlockValue).prod) = 150811814764477236133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_173
      · exact prime_oneHundredTwentyDN_9221
      · exact prime_oneHundredTwentyDN_60607
      · exact prime_oneHundredTwentyDN_6189961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 150811814764477236133) ^ 75405907382238618066 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 150811814764477236133) ^ 50270604921492412044 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 150811814764477236133) ^ 21544544966353890876 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 150811814764477236133) ^ 871744594014319284 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 150811814764477236133) ^ 16355255911991892 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 150811814764477236133) ^ 2488356374090076 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 150811814764477236133) ^ 24363936180612 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_6863
      · exact prime_oneHundredTwentyDN_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_695450024211916627019 : Nat.Prime 695450024211916627019 := by
  apply lucas_primality 695450024211916627019 (2 : ZMod 695450024211916627019)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2500999, 1), (139034446677491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2500999, 1), (139034446677491, 1)] : List FactorBlock).map factorBlockValue).prod) = 695450024211916627019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_2500999
      · exact prime_oneHundredTwentyDN_139034446677491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 695450024211916627019) ^ 347725012105958313509 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 695450024211916627019) ^ 278068893354982 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 695450024211916627019) ^ 5001998 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_829821849978416232493 : Nat.Prime 829821849978416232493 := by
  apply lucas_primality 829821849978416232493 (5 : ZMod 829821849978416232493)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (127, 1), (947, 1), (11437, 1), (1861975811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (127, 1), (947, 1), (11437, 1), (1861975811, 1)] : List FactorBlock).map factorBlockValue).prod) = 829821849978416232493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_127
      · exact prime_oneHundredTwentyDN_947
      · exact prime_oneHundredTwentyDN_11437
      · exact prime_oneHundredTwentyDN_1861975811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 829821849978416232493) ^ 414910924989208116246 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 276607283326138744164 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 6534030314790678996 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 876263833134547236 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 72555901895463516 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 445667363172 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1081687868363620552253 : Nat.Prime 1081687868363620552253 := by
  apply lucas_primality 1081687868363620552253 (2 : ZMod 1081687868363620552253)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1081687868363620552253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_71
      · exact prime_oneHundredTwentyDN_199
      · exact prime_oneHundredTwentyDN_52864081
      · exact prime_oneHundredTwentyDN_362051087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1081687868363620552253) ^ 540843934181810276126 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 15235040399487613412 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 5435617428962917348 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 20461679232892 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 2987666401796 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1205269042013298899237 : Nat.Prime 1205269042013298899237 := by
  apply lucas_primality 1205269042013298899237 (2 : ZMod 1205269042013298899237)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205269042013298899237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_23
      · exact prime_oneHundredTwentyDN_1549
      · exact prime_oneHundredTwentyDN_47713
      · exact prime_oneHundredTwentyDN_341461
      · exact prime_oneHundredTwentyDN_519119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1205269042013298899237) ^ 602634521006649449618 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 52403001826665169532 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 778094927058294964 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 25260810303550372 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 3529741440496276 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 2321758675782044 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_1679191511339295018803 : Nat.Prime 1679191511339295018803 := by
  apply lucas_primality 1679191511339295018803 (2 : ZMod 1679191511339295018803)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (113, 1), (9529907, 1), (70877835001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (113, 1), (9529907, 1), (70877835001, 1)] : List FactorBlock).map factorBlockValue).prod) = 1679191511339295018803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_113
      · exact prime_oneHundredTwentyDN_9529907
      · exact prime_oneHundredTwentyDN_70877835001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1679191511339295018803) ^ 839595755669647509401 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1679191511339295018803) ^ 152653773758117728982 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1679191511339295018803) ^ 14860101870259247954 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1679191511339295018803) ^ 176202297812486 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1679191511339295018803) ^ 23691348802 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_3019418713742564280571 : Nat.Prime 3019418713742564280571 := by
  apply lucas_primality 3019418713742564280571 (10 : ZMod 3019418713742564280571)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (97, 1), (4671071, 1), (222133410637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (97, 1), (4671071, 1), (222133410637, 1)] : List FactorBlock).map factorBlockValue).prod) = 3019418713742564280571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_97
      · exact prime_oneHundredTwentyDN_4671071
      · exact prime_oneHundredTwentyDN_222133410637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3019418713742564280571) ^ 1509709356871282140285 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 1006472904580854760190 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 603883742748512856114 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 31128027976727466810 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 646408224953670 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 13592816610 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_3056734440994420376951 : Nat.Prime 3056734440994420376951 := by
  apply lucas_primality 3056734440994420376951 (13 : ZMod 3056734440994420376951)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (73, 1), (2767, 1), (6451, 1), (46916828279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (73, 1), (2767, 1), (6451, 1), (46916828279, 1)] : List FactorBlock).map factorBlockValue).prod) = 3056734440994420376951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_73
      · exact prime_oneHundredTwentyDN_2767
      · exact prime_oneHundredTwentyDN_6451
      · exact prime_oneHundredTwentyDN_46916828279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3056734440994420376951) ^ 1528367220497210188475 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (13 : ZMod 3056734440994420376951) ^ 611346888198884075390 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (13 : ZMod 3056734440994420376951) ^ 41873074534170142150 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (13 : ZMod 3056734440994420376951) ^ 1104710676181575850 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (13 : ZMod 3056734440994420376951) ^ 473838853045174450 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (13 : ZMod 3056734440994420376951) ^ 65152197050 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_3321529070241708699701 : Nat.Prime 3321529070241708699701 := by
  apply lucas_primality 3321529070241708699701 (2 : ZMod 3321529070241708699701)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (179, 1), (185560283253726743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (179, 1), (185560283253726743, 1)] : List FactorBlock).map factorBlockValue).prod) = 3321529070241708699701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_179
      · exact prime_oneHundredTwentyDN_185560283253726743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3321529070241708699701) ^ 1660764535120854349850 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3321529070241708699701) ^ 664305814048341739940 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3321529070241708699701) ^ 18556028325372674300 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3321529070241708699701) ^ 17900 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_4699160979467066092451 : Nat.Prime 4699160979467066092451 := by
  apply lucas_primality 4699160979467066092451 (7 : ZMod 4699160979467066092451)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (93983219589341321849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (93983219589341321849, 1)] : List FactorBlock).map factorBlockValue).prod) = 4699160979467066092451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_93983219589341321849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4699160979467066092451) ^ 2349580489733533046225 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4699160979467066092451) ^ 939832195893413218490 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4699160979467066092451) ^ 50 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_8993759679696815118617 : Nat.Prime 8993759679696815118617 := by
  apply lucas_primality 8993759679696815118617 (3 : ZMod 8993759679696815118617)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (36265159998777480317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (36265159998777480317, 1)] : List FactorBlock).map factorBlockValue).prod) = 8993759679696815118617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_31
      · exact prime_oneHundredTwentyDN_36265159998777480317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8993759679696815118617) ^ 4496879839848407559308 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8993759679696815118617) ^ 290121279990219842536 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8993759679696815118617) ^ 248 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_9557346059326019093897 : Nat.Prime 9557346059326019093897 := by
  apply lucas_primality 9557346059326019093897 (3 : ZMod 9557346059326019093897)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (607, 1), (4217, 1), (466718517702823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (607, 1), (4217, 1), (466718517702823, 1)] : List FactorBlock).map factorBlockValue).prod) = 9557346059326019093897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_607
      · exact prime_oneHundredTwentyDN_4217
      · exact prime_oneHundredTwentyDN_466718517702823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9557346059326019093897) ^ 4778673029663009546948 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 9557346059326019093897) ^ 15745215913222436728 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 9557346059326019093897) ^ 2266385121964908488 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 9557346059326019093897) ^ 20477752 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_10168288329773995248227 : Nat.Prime 10168288329773995248227 := by
  apply lucas_primality 10168288329773995248227 (2 : ZMod 10168288329773995248227)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (643, 1), (1129558801352365613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (643, 1), (1129558801352365613, 1)] : List FactorBlock).map factorBlockValue).prod) = 10168288329773995248227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_643
      · exact prime_oneHundredTwentyDN_1129558801352365613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10168288329773995248227) ^ 5084144164886997624113 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10168288329773995248227) ^ 1452612618539142178318 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10168288329773995248227) ^ 15813823218933118582 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10168288329773995248227) ^ 9002 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_10251570399530855998699 : Nat.Prime 10251570399530855998699 := by
  apply lucas_primality 10251570399530855998699 (2 : ZMod 10251570399530855998699)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (659, 1), (1063, 1), (813016227818633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (659, 1), (1063, 1), (813016227818633, 1)] : List FactorBlock).map factorBlockValue).prod) = 10251570399530855998699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_659
      · exact prime_oneHundredTwentyDN_1063
      · exact prime_oneHundredTwentyDN_813016227818633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10251570399530855998699) ^ 5125785199765427999349 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10251570399530855998699) ^ 3417190133176951999566 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10251570399530855998699) ^ 15556252503081723822 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10251570399530855998699) ^ 9643998494384624646 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10251570399530855998699) ^ 12609306 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_15923379646956395154271 : Nat.Prime 15923379646956395154271 := by
  apply lucas_primality 15923379646956395154271 (6 : ZMod 15923379646956395154271)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (765941959, 1), (30129387137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (765941959, 1), (30129387137, 1)] : List FactorBlock).map factorBlockValue).prod) = 15923379646956395154271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_23
      · exact prime_oneHundredTwentyDN_765941959
      · exact prime_oneHundredTwentyDN_30129387137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 15923379646956395154271) ^ 7961689823478197577135 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 15923379646956395154271) ^ 5307793215652131718090 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 15923379646956395154271) ^ 3184675929391279030854 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 15923379646956395154271) ^ 692320854215495441490 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 15923379646956395154271) ^ 20789277124530 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 15923379646956395154271) ^ 528499951710 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_47886543588161587791203 : Nat.Prime 47886543588161587791203 := by
  apply lucas_primality 47886543588161587791203 (2 : ZMod 47886543588161587791203)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (14201963, 1), (240844691621461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (14201963, 1), (240844691621461, 1)] : List FactorBlock).map factorBlockValue).prod) = 47886543588161587791203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_14201963
      · exact prime_oneHundredTwentyDN_240844691621461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47886543588161587791203) ^ 23943271794080793895601 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 6840934798308798255886 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 3371825682700454 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 198827482 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_142356036616835933475179 : Nat.Prime 142356036616835933475179 := by
  apply lucas_primality 142356036616835933475179 (6 : ZMod 142356036616835933475179)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (10168288329773995248227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (10168288329773995248227, 1)] : List FactorBlock).map factorBlockValue).prod) = 142356036616835933475179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_10168288329773995248227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 142356036616835933475179) ^ 71178018308417966737589 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 142356036616835933475179) ^ 20336576659547990496454 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 142356036616835933475179) ^ 14 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_259193266026634557332219 : Nat.Prime 259193266026634557332219 := by
  apply lucas_primality 259193266026634557332219 (2 : ZMod 259193266026634557332219)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (71, 1), (19471, 1), (273308408322643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (71, 1), (19471, 1), (273308408322643, 1)] : List FactorBlock).map factorBlockValue).prod) = 259193266026634557332219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_71
      · exact prime_oneHundredTwentyDN_19471
      · exact prime_oneHundredTwentyDN_273308408322643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 259193266026634557332219) ^ 129596633013317278666109 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 37027609432376365333174 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 3650609380656824751158 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 13311759335762649958 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 948354526 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_332481131296975890485423 : Nat.Prime 332481131296975890485423 := by
  apply lucas_primality 332481131296975890485423 (5 : ZMod 332481131296975890485423)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (36502073, 1), (41782361350123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (36502073, 1), (41782361350123, 1)] : List FactorBlock).map factorBlockValue).prod) = 332481131296975890485423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_109
      · exact prime_oneHundredTwentyDN_36502073
      · exact prime_oneHundredTwentyDN_41782361350123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 332481131296975890485423) ^ 166240565648487945242711 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 332481131296975890485423) ^ 3050285608229136609958 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 332481131296975890485423) ^ 9108554774326814 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 332481131296975890485423) ^ 7957451914 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_418512662850455296162327 : Nat.Prime 418512662850455296162327 := by
  apply lucas_primality 418512662850455296162327 (10 : ZMod 418512662850455296162327)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (3321529070241708699701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (3321529070241708699701, 1)] : List FactorBlock).map factorBlockValue).prod) = 418512662850455296162327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_3321529070241708699701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 418512662850455296162327) ^ 209256331425227648081163 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 418512662850455296162327) ^ 139504220950151765387442 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 418512662850455296162327) ^ 59787523264350756594618 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (10 : ZMod 418512662850455296162327) ^ 126 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_710593009332886013740657 : Nat.Prime 710593009332886013740657 := by
  apply lucas_primality 710593009332886013740657 (5 : ZMod 710593009332886013740657)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 2), (15817, 1), (1769293600347029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 2), (15817, 1), (1769293600347029, 1)] : List FactorBlock).map factorBlockValue).prod) = 710593009332886013740657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_23
      · exact prime_oneHundredTwentyDN_15817
      · exact prime_oneHundredTwentyDN_1769293600347029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 710593009332886013740657) ^ 355296504666443006870328 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 710593009332886013740657) ^ 236864336444295337913552 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 710593009332886013740657) ^ 30895348231864609293072 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 710593009332886013740657) ^ 44925903100011760368 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 710593009332886013740657) ^ 401625264 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_878899926231809511221431 : Nat.Prime 878899926231809511221431 := by
  apply lucas_primality 878899926231809511221431 (6 : ZMod 878899926231809511221431)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) = 878899926231809511221431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_797
      · exact prime_oneHundredTwentyDN_125287
      · exact prime_oneHundredTwentyDN_13971226936099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 878899926231809511221431) ^ 439449963115904755610715 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 292966642077269837073810 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 175779985246361902244286 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 125557132318829930174490 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 1102760258760112310190 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 7015092756884668890 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 62907855570 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_960886615321264172664283 : Nat.Prime 960886615321264172664283 := by
  apply lucas_primality 960886615321264172664283 (2 : ZMod 960886615321264172664283)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (104079456961, 1), (1538706810127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (104079456961, 1), (1538706810127, 1)] : List FactorBlock).map factorBlockValue).prod) = 960886615321264172664283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_104079456961
      · exact prime_oneHundredTwentyDN_1538706810127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 960886615321264172664283) ^ 480443307660632086332141 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 960886615321264172664283) ^ 320295538440421390888094 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 960886615321264172664283) ^ 9232240860762 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 960886615321264172664283) ^ 624476741766 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_3931824573686741437833977 : Nat.Prime 3931824573686741437833977 := by
  apply lucas_primality 3931824573686741437833977 (5 : ZMod 3931824573686741437833977)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (661, 1), (727, 1), (17509, 1), (1001989, 1), (58296701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (661, 1), (727, 1), (17509, 1), (1001989, 1), (58296701, 1)] : List FactorBlock).map factorBlockValue).prod) = 3931824573686741437833977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_661
      · exact prime_oneHundredTwentyDN_727
      · exact prime_oneHundredTwentyDN_17509
      · exact prime_oneHundredTwentyDN_1001989
      · exact prime_oneHundredTwentyDN_58296701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3931824573686741437833977) ^ 1965912286843370718916988 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3931824573686741437833977) ^ 5948297388330925019416 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3931824573686741437833977) ^ 5408286896405421510088 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3931824573686741437833977) ^ 224560201821162912664 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3931824573686741437833977) ^ 3924019698506412184 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3931824573686741437833977) ^ 67445061319794776 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_6861676634375057617593509 : Nat.Prime 6861676634375057617593509 := by
  apply lucas_primality 6861676634375057617593509 (2 : ZMod 6861676634375057617593509)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (210430769, 1), (8151940739207033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (210430769, 1), (8151940739207033, 1)] : List FactorBlock).map factorBlockValue).prod) = 6861676634375057617593509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_210430769
      · exact prime_oneHundredTwentyDN_8151940739207033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6861676634375057617593509) ^ 3430838317187528808796754 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6861676634375057617593509) ^ 32607762956828132 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6861676634375057617593509) ^ 841723076 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_7876965526197251196566731 : Nat.Prime 7876965526197251196566731 := by
  apply lucas_primality 7876965526197251196566731 (2 : ZMod 7876965526197251196566731)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (589861, 1), (445131170801101231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (589861, 1), (445131170801101231, 1)] : List FactorBlock).map factorBlockValue).prod) = 7876965526197251196566731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_589861
      · exact prime_oneHundredTwentyDN_445131170801101231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7876965526197251196566731) ^ 3938482763098625598283365 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7876965526197251196566731) ^ 2625655175399083732188910 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7876965526197251196566731) ^ 1575393105239450239313346 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7876965526197251196566731) ^ 13353935124033036930 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7876965526197251196566731) ^ 17695830 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_8622342657854545478386009 : Nat.Prime 8622342657854545478386009 := by
  apply lucas_primality 8622342657854545478386009 (14 : ZMod 8622342657854545478386009)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (19, 1), (23, 1), (1051, 1), (1783, 1), (71663, 1), (470912483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (19, 1), (23, 1), (1051, 1), (1783, 1), (71663, 1), (470912483, 1)] : List FactorBlock).map factorBlockValue).prod) = 8622342657854545478386009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_19
      · exact prime_oneHundredTwentyDN_23
      · exact prime_oneHundredTwentyDN_1051
      · exact prime_oneHundredTwentyDN_1783
      · exact prime_oneHundredTwentyDN_71663
      · exact prime_oneHundredTwentyDN_470912483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 8622342657854545478386009) ^ 4311171328927272739193004 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (14 : ZMod 8622342657854545478386009) ^ 2874114219284848492795336 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (14 : ZMod 8622342657854545478386009) ^ 663257127527272729106616 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (14 : ZMod 8622342657854545478386009) ^ 453807508308133972546632 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (14 : ZMod 8622342657854545478386009) ^ 374884463384980238190696 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (14 : ZMod 8622342657854545478386009) ^ 8203941634495285897608 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (14 : ZMod 8622342657854545478386009) ^ 4835862399245398473576 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (14 : ZMod 8622342657854545478386009) ^ 120317913816816843816 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (14 : ZMod 8622342657854545478386009) ^ 18309862169983176 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_19808995544867172759196229 : Nat.Prime 19808995544867172759196229 := by
  apply lucas_primality 19808995544867172759196229 (2 : ZMod 19808995544867172759196229)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (37, 1), (115183, 1), (166002379433901781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (37, 1), (115183, 1), (166002379433901781, 1)] : List FactorBlock).map factorBlockValue).prod) = 19808995544867172759196229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_37
      · exact prime_oneHundredTwentyDN_115183
      · exact prime_oneHundredTwentyDN_166002379433901781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19808995544867172759196229) ^ 9904497772433586379598114 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 19808995544867172759196229) ^ 2829856506409596108456604 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 19808995544867172759196229) ^ 535378257969383047545844 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 19808995544867172759196229) ^ 171978465093522245116 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 19808995544867172759196229) ^ 119329588 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_58239747985360710714845399 : Nat.Prime 58239747985360710714845399 := by
  apply lucas_primality 58239747985360710714845399 (11 : ZMod 58239747985360710714845399)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2333, 1), (2372670067, 1), (5260625686909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2333, 1), (2372670067, 1), (5260625686909, 1)] : List FactorBlock).map factorBlockValue).prod) = 58239747985360710714845399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_2333
      · exact prime_oneHundredTwentyDN_2372670067
      · exact prime_oneHundredTwentyDN_5260625686909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 58239747985360710714845399) ^ 29119873992680355357422699 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (11 : ZMod 58239747985360710714845399) ^ 24963458202040596105806 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (11 : ZMod 58239747985360710714845399) ^ 24546079455117394 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (11 : ZMod 58239747985360710714845399) ^ 11070878532622 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_234887460417779290234045351 : Nat.Prime 234887460417779290234045351 := by
  apply lucas_primality 234887460417779290234045351 (3 : ZMod 234887460417779290234045351)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (142356036616835933475179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (142356036616835933475179, 1)] : List FactorBlock).map factorBlockValue).prod) = 234887460417779290234045351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_142356036616835933475179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 234887460417779290234045351) ^ 117443730208889645117022675 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 234887460417779290234045351) ^ 78295820139259763411348450 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 234887460417779290234045351) ^ 46977492083555858046809070 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 234887460417779290234045351) ^ 21353405492525390021276850 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 234887460417779290234045351) ^ 1650 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_462123863492959906519098997 : Nat.Prime 462123863492959906519098997 := by
  apply lucas_primality 462123863492959906519098997 (5 : ZMod 462123863492959906519098997)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1109, 1), (43866235967, 1), (263872406687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1109, 1), (43866235967, 1), (263872406687, 1)] : List FactorBlock).map factorBlockValue).prod) = 462123863492959906519098997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_1109
      · exact prime_oneHundredTwentyDN_43866235967
      · exact prime_oneHundredTwentyDN_263872406687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 462123863492959906519098997) ^ 231061931746479953259549498 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 462123863492959906519098997) ^ 154041287830986635506366332 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 462123863492959906519098997) ^ 416703213248836705607844 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 462123863492959906519098997) ^ 10534841964571788 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 462123863492959906519098997) ^ 1751315604746508 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_806091057342833473303201091 : Nat.Prime 806091057342833473303201091 := by
  apply lucas_primality 806091057342833473303201091 (2 : ZMod 806091057342833473303201091)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (311, 1), (259193266026634557332219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (311, 1), (259193266026634557332219, 1)] : List FactorBlock).map factorBlockValue).prod) = 806091057342833473303201091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_311
      · exact prime_oneHundredTwentyDN_259193266026634557332219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 806091057342833473303201091) ^ 403045528671416736651600545 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 806091057342833473303201091) ^ 161218211468566694660640218 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 806091057342833473303201091) ^ 2591932660266345573322190 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 806091057342833473303201091) ^ 3110 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_909436064694478790393355077 : Nat.Prime 909436064694478790393355077 := by
  apply lucas_primality 909436064694478790393355077 (2 : ZMod 909436064694478790393355077)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4171314503, 1), (54505364198768423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4171314503, 1), (54505364198768423, 1)] : List FactorBlock).map factorBlockValue).prod) = 909436064694478790393355077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_4171314503
      · exact prime_oneHundredTwentyDN_54505364198768423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 909436064694478790393355077) ^ 454718032347239395196677538 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 909436064694478790393355077) ^ 218021456795073692 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 909436064694478790393355077) ^ 16685258012 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_2446069415385149850023506759 : Nat.Prime 2446069415385149850023506759 := by
  apply lucas_primality 2446069415385149850023506759 (7 : ZMod 2446069415385149850023506759)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (58239747985360710714845399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (58239747985360710714845399, 1)] : List FactorBlock).map factorBlockValue).prod) = 2446069415385149850023506759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_58239747985360710714845399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2446069415385149850023506759) ^ 1223034707692574925011753379 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 2446069415385149850023506759) ^ 815356471795049950007835586 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 2446069415385149850023506759) ^ 349438487912164264289072394 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (7 : ZMod 2446069415385149850023506759) ^ 42 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_2579491383497067114570243491 : Nat.Prime 2579491383497067114570243491 := by
  apply lucas_primality 2579491383497067114570243491 (2 : ZMod 2579491383497067114570243491)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (103573, 1), (10089149659, 1), (35264271901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (103573, 1), (10089149659, 1), (35264271901, 1)] : List FactorBlock).map factorBlockValue).prod) = 2579491383497067114570243491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_103573
      · exact prime_oneHundredTwentyDN_10089149659
      · exact prime_oneHundredTwentyDN_35264271901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2579491383497067114570243491) ^ 1289745691748533557285121745 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2579491383497067114570243491) ^ 515898276699413422914048698 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2579491383497067114570243491) ^ 368498769071009587795749070 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2579491383497067114570243491) ^ 24905056177740020223130 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2579491383497067114570243491) ^ 255669850352159110 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2579491383497067114570243491) ^ 73147444834212490 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_6168348960536464839189712697 : Nat.Prime 6168348960536464839189712697 := by
  apply lucas_primality 6168348960536464839189712697 (3 : ZMod 6168348960536464839189712697)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (137, 1), (1243169, 1), (4527184655447032079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (137, 1), (1243169, 1), (4527184655447032079, 1)] : List FactorBlock).map factorBlockValue).prod) = 6168348960536464839189712697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_137
      · exact prime_oneHundredTwentyDN_1243169
      · exact prime_oneHundredTwentyDN_4527184655447032079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6168348960536464839189712697) ^ 3084174480268232419594856348 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 6168348960536464839189712697) ^ 45024444967419451380946808 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 6168348960536464839189712697) ^ 4961794382369947158584 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 6168348960536464839189712697) ^ 1362513224 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_7466948741702036384282283793 : Nat.Prime 7466948741702036384282283793 := by
  apply lucas_primality 7466948741702036384282283793 (5 : ZMod 7466948741702036384282283793)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 7466948741702036384282283793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_7
      · exact prime_oneHundredTwentyDN_41
      · exact prime_oneHundredTwentyDN_397
      · exact prime_oneHundredTwentyDN_13617913
      · exact prime_oneHundredTwentyDN_100257985466497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7466948741702036384282283793) ^ 3733474370851018192141141896 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7466948741702036384282283793) ^ 2488982913900678794760761264 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7466948741702036384282283793) ^ 1066706963100290912040326256 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7466948741702036384282283793) ^ 182120701017122838641031312 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7466948741702036384282283793) ^ 18808435117637371245043536 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7466948741702036384282283793) ^ 548318141091225680784 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7466948741702036384282283793) ^ 74477346686736 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_12897456917485335572851217459 : Nat.Prime 12897456917485335572851217459 := by
  apply lucas_primality 12897456917485335572851217459 (2 : ZMod 12897456917485335572851217459)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (14753, 1), (3056734440994420376951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (14753, 1), (3056734440994420376951, 1)] : List FactorBlock).map factorBlockValue).prod) = 12897456917485335572851217459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_14753
      · exact prime_oneHundredTwentyDN_3056734440994420376951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12897456917485335572851217459) ^ 6448728458742667786425608729 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 12897456917485335572851217459) ^ 1172496083407757779350110678 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 12897456917485335572851217459) ^ 992112070575795044065478266 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 12897456917485335572851217459) ^ 874226050124404227807986 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 12897456917485335572851217459) ^ 4219358 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_15763558454704299033484821337 : Nat.Prime 15763558454704299033484821337 := by
  apply lucas_primality 15763558454704299033484821337 (5 : ZMod 15763558454704299033484821337)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) = 15763558454704299033484821337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_607213
      · exact prime_oneHundredTwentyDN_1081687868363620552253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15763558454704299033484821337) ^ 7881779227352149516742410668 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 15763558454704299033484821337) ^ 5254519484901433011161607112 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 15763558454704299033484821337) ^ 25960508840726893254072 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (5 : ZMod 15763558454704299033484821337) ^ 14573112 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_23645337682056448550227232011 : Nat.Prime 23645337682056448550227232011 := by
  apply lucas_primality 23645337682056448550227232011 (3 : ZMod 23645337682056448550227232011)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056448550227232011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_5
      · exact prime_oneHundredTwentyDN_11
      · exact prime_oneHundredTwentyDN_461
      · exact prime_oneHundredTwentyDN_69997
      · exact prime_oneHundredTwentyDN_2220502305087140441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23645337682056448550227232011) ^ 11822668841028224275113616005 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 7881779227352149516742410670 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 4729067536411289710045446402 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 2149576152914222595475202910 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 51291404950230907918063410 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 337805015672906675289330 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 10648643610 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_47290675364112897100454464013 : Nat.Prime 47290675364112897100454464013 := by
  apply lucas_primality 47290675364112897100454464013 (2 : ZMod 47290675364112897100454464013)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (521, 1), (23096547757, 1), (57793874370247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (521, 1), (23096547757, 1), (57793874370247, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112897100454464013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_17
      · exact prime_oneHundredTwentyDN_521
      · exact prime_oneHundredTwentyDN_23096547757
      · exact prime_oneHundredTwentyDN_57793874370247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47290675364112897100454464013) ^ 23645337682056448550227232006 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 47290675364112897100454464013) ^ 2781804433183111594144380236 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 47290675364112897100454464013) ^ 90769050602903833206246572 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 47290675364112897100454464013) ^ 2047521381189110716 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (2 : ZMod 47290675364112897100454464013) ^ 818264493934996 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyDN_70936013046169345650681696007 : Nat.Prime 70936013046169345650681696007 := by
  apply lucas_primality 70936013046169345650681696007 (3 : ZMod 70936013046169345650681696007)
  · rw [← oneHundredTwentyDNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (909436064694478790393355077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (909436064694478790393355077, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169345650681696007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyDN_2
      · exact prime_oneHundredTwentyDN_3
      · exact prime_oneHundredTwentyDN_13
      · exact prime_oneHundredTwentyDN_909436064694478790393355077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 70936013046169345650681696007) ^ 35468006523084672825340848003 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 70936013046169345650681696007) ^ 23645337682056448550227232002 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 70936013046169345650681696007) ^ 5456616388166872742360130462 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide
    · change (3 : ZMod 70936013046169345650681696007) ^ 78 ≠ 1
      rw [← oneHundredTwentyDNFastPow_eq_pow]
      decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392000 : Nat.totient 141872026092338691301363392000 = 37832319506721499351326720000 := by
  rw [← show ((([(2, 9), (3, 1), (5, 3), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_171401, prime_oneHundredTwentyDN_714027719, prime_oneHundredTwentyDN_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392001 : Nat.totient 141872026092338691301363392001 = 138572662915223102843675592768 := by
  rw [← show ((([(43, 1), (13023389, 1), (44805067, 1), (5654278184189, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_43, prime_oneHundredTwentyDN_13023389, prime_oneHundredTwentyDN_44805067, prime_oneHundredTwentyDN_5654278184189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392002 : Nat.totient 141872026092338691301363392002 = 66763237027560640744872717568 := by
  rw [← show ((([(2, 1), (17, 1), (1018559, 1), (17468093, 1), (234523392557819, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_17, prime_oneHundredTwentyDN_1018559, prime_oneHundredTwentyDN_17468093, prime_oneHundredTwentyDN_234523392557819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392003 : Nat.totient 141872026092338691301363392003 = 91970933733546350449539288960 := by
  rw [← show ((([(3, 1), (37, 1), (1699, 1), (276099113611, 1), (2724679354157, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_37, prime_oneHundredTwentyDN_1699, prime_oneHundredTwentyDN_276099113611, prime_oneHundredTwentyDN_2724679354157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392004 : Nat.totient 141872026092338691301363392004 = 70466238125333787070213605000 := by
  rw [← show ((([(2, 2), (151, 1), (234887460417779290234045351, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_151, prime_oneHundredTwentyDN_234887460417779290234045351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392005 : Nat.totient 141872026092338691301363392005 = 103179655339882684582809739600 := by
  rw [← show ((([(5, 1), (11, 1), (2579491383497067114570243491, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_11, prime_oneHundredTwentyDN_2579491383497067114570243491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392006 : Nat.totient 141872026092338691301363392006 = 39545671008721428668655562752 := by
  rw [← show ((([(2, 1), (3, 2), (7, 2), (47, 1), (313, 1), (55413389, 1), (197320078064177, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_7, prime_oneHundredTwentyDN_47, prime_oneHundredTwentyDN_313, prime_oneHundredTwentyDN_55413389, prime_oneHundredTwentyDN_197320078064177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392007 : Nat.totient 141872026092338691301363392007 = 138363409345535984698488192960 := by
  rw [← show ((([(41, 1), (2879, 1), (559939, 1), (2146498216888109467, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_41, prime_oneHundredTwentyDN_2879, prime_oneHundredTwentyDN_559939, prime_oneHundredTwentyDN_2146498216888109467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392008 : Nat.totient 141872026092338691301363392008 = 67356515489913542860938268672 := by
  rw [← show ((([(2, 3), (23, 1), (137, 1), (1243169, 1), (4527184655447032079, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_23, prime_oneHundredTwentyDN_137, prime_oneHundredTwentyDN_1243169, prime_oneHundredTwentyDN_4527184655447032079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392009 : Nat.totient 141872026092338691301363392009 = 94500584803605626600077516800 := by
  rw [← show ((([(3, 1), (1451, 1), (6689, 1), (71999, 1), (676337, 1), (100059262279, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_1451, prime_oneHundredTwentyDN_6689, prime_oneHundredTwentyDN_71999, prime_oneHundredTwentyDN_676337, prime_oneHundredTwentyDN_100059262279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392010 : Nat.totient 141872026092338691301363392010 = 51924336943515372873756152640 := by
  rw [← show ((([(2, 1), (5, 1), (19, 1), (31, 1), (503, 1), (47886543588161587791203, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_19, prime_oneHundredTwentyDN_31, prime_oneHundredTwentyDN_503, prime_oneHundredTwentyDN_47886543588161587791203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392011 : Nat.totient 141872026092338691301363392011 = 141872026080940415560371046800 := by
  rw [← show ((([(12446797171, 1), (11398275728545548041, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_12446797171, prime_oneHundredTwentyDN_11398275728545548041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392012 : Nat.totient 141872026092338691301363392012 = 43652931105334981938881043648 := by
  rw [← show ((([(2, 2), (3, 1), (13, 1), (909436064694478790393355077, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_13, prime_oneHundredTwentyDN_909436064694478790393355077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392013 : Nat.totient 141872026092338691301363392013 = 121604569902473771645477577216 := by
  rw [← show ((([(7, 1), (5321087, 1), (117195809, 1), (32500219188373, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_7, prime_oneHundredTwentyDN_5321087, prime_oneHundredTwentyDN_117195809, prime_oneHundredTwentyDN_32500219188373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392014 : Nat.totient 141872026092338691301363392014 = 70936013046169345650681696006 := by
  rw [← show ((([(2, 1), (70936013046169345650681696007, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_70936013046169345650681696007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392015 : Nat.totient 141872026092338691301363392015 = 74599279131199631480971504128 := by
  rw [← show ((([(3, 2), (5, 1), (89, 1), (347, 1), (2755243, 1), (37051420944511243, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_89, prime_oneHundredTwentyDN_347, prime_oneHundredTwentyDN_2755243, prime_oneHundredTwentyDN_37051420944511243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392016 : Nat.totient 141872026092338691301363392016 = 64487284587426677864256087200 := by
  rw [← show ((([(2, 4), (11, 1), (806091057342833473303201091, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_11, prime_oneHundredTwentyDN_806091057342833473303201091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392017 : Nat.totient 141872026092338691301363392017 = 141872026092220303195095863616 := by
  rw [← show ((([(1198375974329, 1), (118386907891554073, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_1198375974329, prime_oneHundredTwentyDN_118386907891554073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392018 : Nat.totient 141872026092338691301363392018 = 47290675364006865937955655456 := by
  rw [← show ((([(2, 1), (3, 1), (446011079209, 1), (53015135238325067, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_446011079209, prime_oneHundredTwentyDN_53015135238325067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392019 : Nat.totient 141872026092338691301363392019 = 133407072404862348695004744192 := by
  rw [← show ((([(17, 1), (1117, 1), (288836296843, 1), (25866812093597, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_17, prime_oneHundredTwentyDN_1117, prime_oneHundredTwentyDN_288836296843, prime_oneHundredTwentyDN_25866812093597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392020 : Nat.totient 141872026092338691301363392020 = 48599650320914138732500193280 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (1153, 1), (878899926231809511221431, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_7, prime_oneHundredTwentyDN_1153, prime_oneHundredTwentyDN_878899926231809511221431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392021 : Nat.totient 141872026092338691301363392021 = 92945565620741490597277804800 := by
  rw [← show ((([(3, 1), (61, 1), (1091, 1), (710593009332886013740657, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_61, prime_oneHundredTwentyDN_1091, prime_oneHundredTwentyDN_710593009332886013740657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392022 : Nat.totient 141872026092338691301363392022 = 68489943630784195800658189224 := by
  rw [← show ((([(2, 1), (29, 1), (2446069415385149850023506759, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_29, prime_oneHundredTwentyDN_2446069415385149850023506759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392023 : Nat.totient 141872026092338691301363392023 = 141667978558358949680706508800 := by
  rw [← show ((([(701, 1), (85243, 1), (370615897, 1), (6406133481313, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_701, prime_oneHundredTwentyDN_85243, prime_oneHundredTwentyDN_370615897, prime_oneHundredTwentyDN_6406133481313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392024 : Nat.totient 141872026092338691301363392024 = 47290597482586374919730982528 := by
  rw [← show ((([(2, 3), (3, 3), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_607213, prime_oneHundredTwentyDN_1081687868363620552253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392025 : Nat.totient 141872026092338691301363392025 = 104767034645704695043498785600 := by
  rw [← show ((([(5, 2), (13, 1), (14757462491, 1), (29580241950103007, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_13, prime_oneHundredTwentyDN_14757462491, prime_oneHundredTwentyDN_29580241950103007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392026 : Nat.totient 141872026092338691301363392026 = 69519193067884637984522757120 := by
  rw [← show ((([(2, 1), (59, 1), (569, 1), (757, 1), (21610411, 1), (129164626112089, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_59, prime_oneHundredTwentyDN_569, prime_oneHundredTwentyDN_757, prime_oneHundredTwentyDN_21610411, prime_oneHundredTwentyDN_129164626112089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392027 : Nat.totient 141872026092338691301363392027 = 73083878434138948888731444480 := by
  rw [← show ((([(3, 1), (7, 1), (11, 1), (179, 1), (359, 1), (9557346059326019093897, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_7, prime_oneHundredTwentyDN_11, prime_oneHundredTwentyDN_179, prime_oneHundredTwentyDN_359, prime_oneHundredTwentyDN_9557346059326019093897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392028 : Nat.totient 141872026092338691301363392028 = 70935981199410051737886932640 := by
  rw [← show ((([(2, 2), (2227417, 1), (15923379646956395154271, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_2227417, prime_oneHundredTwentyDN_15923379646956395154271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392029 : Nat.totient 141872026092338691301363392029 = 133015433558260706608407662592 := by
  rw [← show ((([(19, 1), (97, 1), (35023, 1), (601543, 1), (32746729, 1), (111579263, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_19, prime_oneHundredTwentyDN_97, prime_oneHundredTwentyDN_35023, prime_oneHundredTwentyDN_601543, prime_oneHundredTwentyDN_32746729, prime_oneHundredTwentyDN_111579263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392030 : Nat.totient 141872026092338691301363392030 = 37827536633220295973060824320 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_7561, prime_oneHundredTwentyDN_2416168199, prime_oneHundredTwentyDN_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392031 : Nat.totient 141872026092338691301363392031 = 135703677131802226462173679312 := by
  rw [← show ((([(23, 1), (6168348960536464839189712697, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_23, prime_oneHundredTwentyDN_6168348960536464839189712697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392032 : Nat.totient 141872026092338691301363392032 = 68093553286920526626065459200 := by
  rw [← show ((([(2, 5), (53, 1), (71, 1), (131, 1), (8993759679696815118617, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_53, prime_oneHundredTwentyDN_71, prime_oneHundredTwentyDN_131, prime_oneHundredTwentyDN_8993759679696815118617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392033 : Nat.totient 141872026092338691301363392033 = 94581350728225794200908928016 := by
  rw [← show ((([(3, 2), (15763558454704299033484821337, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_15763558454704299033484821337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392034 : Nat.totient 141872026092338691301363392034 = 60802296896714809952947321152 := by
  rw [← show ((([(2, 1), (7, 1), (39629873954807, 1), (255709017924433, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_7, prime_oneHundredTwentyDN_39629873954807, prime_oneHundredTwentyDN_255709017924433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392035 : Nat.totient 141872026092338691301363392035 = 113459419049086748604457370880 := by
  rw [← show ((([(5, 1), (2971, 1), (626696252953, 1), (15239370115789, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_2971, prime_oneHundredTwentyDN_626696252953, prime_oneHundredTwentyDN_15239370115789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392036 : Nat.totient 141872026092338691301363392036 = 44423441234320550753494241280 := by
  rw [← show ((([(2, 2), (3, 1), (17, 1), (521, 1), (23096547757, 1), (57793874370247, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_17, prime_oneHundredTwentyDN_521, prime_oneHundredTwentyDN_23096547757, prime_oneHundredTwentyDN_57793874370247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392037 : Nat.totient 141872026092338691301363392037 = 141022483271267943851727185952 := by
  rw [← show ((([(167, 1), (14492537, 1), (58618659408858889003, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_167, prime_oneHundredTwentyDN_14492537, prime_oneHundredTwentyDN_58618659408858889003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392038 : Nat.totient 141872026092338691301363392038 = 59522689345085590009011648000 := by
  rw [← show ((([(2, 1), (11, 2), (13, 1), (14753, 1), (3056734440994420376951, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_11, prime_oneHundredTwentyDN_13, prime_oneHundredTwentyDN_14753, prime_oneHundredTwentyDN_3056734440994420376951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392039 : Nat.totient 141872026092338691301363392039 = 94581350728225794200908928024 := by
  rw [← show ((([(3, 1), (47290675364112897100454464013, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_47290675364112897100454464013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392040 : Nat.totient 141872026092338691301363392040 = 55213287784522733734017435648 := by
  rw [← show ((([(2, 3), (5, 1), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_37, prime_oneHundredTwentyDN_31177, prime_oneHundredTwentyDN_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392041 : Nat.totient 141872026092338691301363392041 = 116264011166671427661324934800 := by
  rw [← show ((([(7, 1), (31, 1), (83, 1), (7876965526197251196566731, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_7, prime_oneHundredTwentyDN_31, prime_oneHundredTwentyDN_83, prime_oneHundredTwentyDN_7876965526197251196566731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392042 : Nat.totient 141872026092338691301363392042 = 47290671191412751828886701800 := by
  rw [← show ((([(2, 1), (3, 2), (11333351, 1), (695450024211916627019, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_11333351, prime_oneHundredTwentyDN_695450024211916627019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392043 : Nat.totient 141872026092338691301363392043 = 140781083385173194700630692000 := by
  rw [← show ((([(251, 1), (269, 1), (342179, 1), (6140693439609514343, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_251, prime_oneHundredTwentyDN_269, prime_oneHundredTwentyDN_342179, prime_oneHundredTwentyDN_6140693439609514343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392044 : Nat.totient 141872026092338691301363392044 = 69285074501410090434149532480 := by
  rw [← show ((([(2, 2), (43, 1), (54829, 1), (487066871, 1), (30886550519203, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_43, prime_oneHundredTwentyDN_54829, prime_oneHundredTwentyDN_487066871, prime_oneHundredTwentyDN_30886550519203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392045 : Nat.totient 141872026092338691301363392045 = 75564307122278168809074600000 := by
  rw [← show ((([(3, 1), (5, 1), (751, 1), (3594403, 1), (3503795954666829551, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_751, prime_oneHundredTwentyDN_3594403, prime_oneHundredTwentyDN_3503795954666829551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392046 : Nat.totient 141872026092338691301363392046 = 70936013046032428443210949368 := by
  rw [← show ((([(2, 1), (518096174909, 1), (136916689374571747, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_518096174909, prime_oneHundredTwentyDN_136916689374571747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392047 : Nat.totient 141872026092338691301363392047 = 141149854215543740150521272384 := by
  rw [← show ((([(197, 1), (70249, 1), (10251570399530855998699, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_197, prime_oneHundredTwentyDN_70249, prime_oneHundredTwentyDN_10251570399530855998699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392048 : Nat.totient 141872026092338691301363392048 = 37370457330634725440398295040 := by
  rw [← show ((([(2, 4), (3, 1), (7, 1), (19, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_7, prime_oneHundredTwentyDN_19, prime_oneHundredTwentyDN_41, prime_oneHundredTwentyDN_397, prime_oneHundredTwentyDN_13617913, prime_oneHundredTwentyDN_100257985466497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392049 : Nat.totient 141872026092338691301363392049 = 128974569174853355728512174580 := by
  rw [← show ((([(11, 1), (12897456917485335572851217459, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_11, prime_oneHundredTwentyDN_12897456917485335572851217459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392050 : Nat.totient 141872026092338691301363392050 = 56748810170696719765138871040 := by
  rw [← show ((([(2, 1), (5, 2), (213150073, 1), (13311937837557174217, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_213150073, prime_oneHundredTwentyDN_13311937837557174217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392051 : Nat.totient 141872026092338691301363392051 = 84295314395576483135071943808 := by
  rw [← show ((([(3, 3), (13, 1), (29, 1), (100076147, 1), (139271123883117227, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_13, prime_oneHundredTwentyDN_29, prime_oneHundredTwentyDN_100076147, prime_oneHundredTwentyDN_139271123883117227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392052 : Nat.totient 141872026092338691301363392052 = 70909214399780712478206405120 := by
  rw [← show ((([(2, 2), (2647, 1), (47591935099, 1), (281546073328321, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_2647, prime_oneHundredTwentyDN_47591935099, prime_oneHundredTwentyDN_281546073328321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392053 : Nat.totient 141872026092338691301363392053 = 130680205801888527187325982720 := by
  rw [← show ((([(17, 1), (47, 1), (24133, 1), (33323112871, 1), (220796972729, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_17, prime_oneHundredTwentyDN_47, prime_oneHundredTwentyDN_24133, prime_oneHundredTwentyDN_33323112871, prime_oneHundredTwentyDN_220796972729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392054 : Nat.totient 141872026092338691301363392054 = 45035076761518625029489856384 := by
  rw [← show ((([(2, 1), (3, 1), (23, 1), (227, 1), (235397, 1), (2276699, 1), (8450556055043, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_23, prime_oneHundredTwentyDN_227, prime_oneHundredTwentyDN_235397, prime_oneHundredTwentyDN_2276699, prime_oneHundredTwentyDN_8450556055043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392055 : Nat.totient 141872026092338691301363392055 = 97283653476792100630216618560 := by
  rw [← show ((([(5, 1), (7, 2), (4517543, 1), (4980897683, 1), (25734798431, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_7, prime_oneHundredTwentyDN_4517543, prime_oneHundredTwentyDN_4980897683, prime_oneHundredTwentyDN_25734798431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392056 : Nat.totient 141872026092338691301363392056 = 70873728476942264034678604800 := by
  rw [← show ((([(2, 3), (1697, 1), (3461, 1), (3019418713742564280571, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_1697, prime_oneHundredTwentyDN_3461, prime_oneHundredTwentyDN_3019418713742564280571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392057 : Nat.totient 141872026092338691301363392057 = 94580513702900093290316377392 := by
  rw [← show ((([(3, 1), (112997, 1), (418512662850455296162327, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_112997, prime_oneHundredTwentyDN_418512662850455296162327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392058 : Nat.totient 141872026092338691301363392058 = 70270702351793226153175169088 := by
  rw [← show ((([(2, 1), (163, 1), (317, 1), (9103, 1), (150811814764477236133, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_163, prime_oneHundredTwentyDN_317, prime_oneHundredTwentyDN_9103, prime_oneHundredTwentyDN_150811814764477236133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392059 : Nat.totient 141872026092338691301363392059 = 141869304413352835317048960000 := by
  rw [← show ((([(70501, 1), (200131, 1), (316566433, 1), (31763054933, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_70501, prime_oneHundredTwentyDN_200131, prime_oneHundredTwentyDN_316566433, prime_oneHundredTwentyDN_31763054933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392060 : Nat.totient 141872026092338691301363392060 = 34318122479790989678203392000 := by
  rw [← show ((([(2, 2), (3, 2), (5, 1), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_11, prime_oneHundredTwentyDN_461, prime_oneHundredTwentyDN_69997, prime_oneHundredTwentyDN_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392061 : Nat.totient 141872026092338691301363392061 = 141871693611207394325472479932 := by
  rw [← show ((([(426707, 1), (332481131296975890485423, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_426707, prime_oneHundredTwentyDN_332481131296975890485423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392062 : Nat.totient 141872026092338691301363392062 = 59208124016620820694171363840 := by
  rw [← show ((([(2, 1), (7, 1), (73, 1), (79, 1), (27431, 1), (64058555872321487129, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_7, prime_oneHundredTwentyDN_73, prime_oneHundredTwentyDN_79, prime_oneHundredTwentyDN_27431, prime_oneHundredTwentyDN_64058555872321487129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392063 : Nat.totient 141872026092338691301363392063 = 94581350728224136475863688984 := by
  rw [← show ((([(3, 1), (61638694796963, 1), (767223827822567, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_61638694796963, prime_oneHundredTwentyDN_767223827822567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392064 : Nat.totient 141872026092338691301363392064 = 64481061225305239734586042368 := by
  rw [← show ((([(2, 6), (13, 1), (67, 1), (3067, 1), (829821849978416232493, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_13, prime_oneHundredTwentyDN_67, prime_oneHundredTwentyDN_3067, prime_oneHundredTwentyDN_829821849978416232493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392065 : Nat.totient 141872026092338691301363392065 = 113497620873866057917792371312 := by
  rw [← show ((([(5, 1), (23642614645087, 1), (1200138209940499, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_23642614645087, prime_oneHundredTwentyDN_1200138209940499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392066 : Nat.totient 141872026092338691301363392066 = 47290675364112897100454464020 := by
  rw [← show ((([(2, 1), (3, 1), (23645337682056448550227232011, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_23645337682056448550227232011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392067 : Nat.totient 141872026092338691301363392067 = 134405077350636654917081108256 := by
  rw [← show ((([(19, 1), (7466948741702036384282283793, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_19, prime_oneHundredTwentyDN_7466948741702036384282283793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392068 : Nat.totient 141872026092338691301363392068 = 70822121193846004896013464960 := by
  rw [← show ((([(2, 2), (653, 1), (13463, 1), (10868173573, 1), (371214717911, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_653, prime_oneHundredTwentyDN_13463, prime_oneHundredTwentyDN_10868173573, prime_oneHundredTwentyDN_371214717911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392069 : Nat.totient 141872026092338691301363392069 = 81069729081670061711523992160 := by
  rw [← show ((([(3, 2), (7, 1), (711437231, 1), (3165334654942473973, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_7, prime_oneHundredTwentyDN_711437231, prime_oneHundredTwentyDN_3165334654942473973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392070 : Nat.totient 141872026092338691301363392070 = 53410645021623575608586984448 := by
  rw [← show ((([(2, 1), (5, 1), (17, 1), (559319647, 1), (1492065108799822793, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_17, prime_oneHundredTwentyDN_559319647, prime_oneHundredTwentyDN_1492065108799822793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392071 : Nat.totient 141872026092338691301363392071 = 128942996546913134108677005600 := by
  rw [← show ((([(11, 1), (5077, 1), (20903, 1), (121531344317416447031, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_11, prime_oneHundredTwentyDN_5077, prime_oneHundredTwentyDN_20903, prime_oneHundredTwentyDN_121531344317416447031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392072 : Nat.totient 141872026092338691301363392072 = 45765156991158443238976235520 := by
  rw [← show ((([(2, 3), (3, 1), (31, 1), (3599009, 1), (52983531609217552957, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_31, prime_oneHundredTwentyDN_3599009, prime_oneHundredTwentyDN_52983531609217552957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392073 : Nat.totient 141872026092338691301363392073 = 141872021718050559616568496000 := by
  rw [← show ((([(36327593, 1), (302547061, 1), (12908245282301, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_36327593, prime_oneHundredTwentyDN_302547061, prime_oneHundredTwentyDN_12908245282301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392074 : Nat.totient 141872026092338691301363392074 = 70742714394899002137114507984 := by
  rw [← show ((([(2, 1), (367, 1), (5653909, 1), (34186284054161410879, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_367, prime_oneHundredTwentyDN_5653909, prime_oneHundredTwentyDN_34186284054161410879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392075 : Nat.totient 141872026092338691301363392075 = 75323912657956128479797862400 := by
  rw [← show ((([(3, 1), (5, 2), (271, 1), (1217, 1), (4440187, 1), (1291737826932829, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_271, prime_oneHundredTwentyDN_1217, prime_oneHundredTwentyDN_4440187, prime_oneHundredTwentyDN_1291737826932829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392076 : Nat.totient 141872026092338691301363392076 = 60802296868432817245762659840 := by
  rw [← show ((([(2, 2), (7, 1), (2149724321, 1), (2356980392894937077, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_7, prime_oneHundredTwentyDN_2149724321, prime_oneHundredTwentyDN_2356980392894937077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392077 : Nat.totient 141872026092338691301363392077 = 121834733188476429477135014400 := by
  rw [← show ((([(13, 1), (23, 1), (37, 1), (2729, 1), (4699160979467066092451, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_13, prime_oneHundredTwentyDN_23, prime_oneHundredTwentyDN_37, prime_oneHundredTwentyDN_2729, prime_oneHundredTwentyDN_4699160979467066092451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392078 : Nat.totient 141872026092338691301363392078 = 47243709508235616461553511680 := by
  rw [← show ((([(2, 1), (3, 4), (1223, 1), (8849, 1), (15971, 1), (5066744382093707, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_1223, prime_oneHundredTwentyDN_8849, prime_oneHundredTwentyDN_15971, prime_oneHundredTwentyDN_5066744382093707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392079 : Nat.totient 141872026092338691301363392079 = 141409902228845731394844292776 := by
  rw [← show ((([(307, 1), (462123863492959906519098997, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_307, prime_oneHundredTwentyDN_462123863492959906519098997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392080 : Nat.totient 141872026092338691301363392080 = 54186119189045119868986720256 := by
  rw [← show ((([(2, 4), (5, 1), (29, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_29, prime_oneHundredTwentyDN_113, prime_oneHundredTwentyDN_449, prime_oneHundredTwentyDN_1205269042013298899237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392081 : Nat.totient 141872026092338691301363392081 = 94142101965223870133999539200 := by
  rw [← show ((([(3, 1), (263, 1), (1471, 1), (6047, 1), (3364231441, 1), (6008710237, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_263, prime_oneHundredTwentyDN_1471, prime_oneHundredTwentyDN_6047, prime_oneHundredTwentyDN_3364231441, prime_oneHundredTwentyDN_6008710237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392082 : Nat.totient 141872026092338691301363392082 = 62868930184543205503946880000 := by
  rw [← show ((([(2, 1), (11, 1), (61, 1), (157, 1), (401, 1), (1679191511339295018803, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_11, prime_oneHundredTwentyDN_61, prime_oneHundredTwentyDN_157, prime_oneHundredTwentyDN_401, prime_oneHundredTwentyDN_1679191511339295018803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392083 : Nat.totient 141872026092338691301363392083 = 121603810672033434557803095840 := by
  rw [← show ((([(7, 1), (155291, 1), (2655560587, 1), (49146911386957, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_7, prime_oneHundredTwentyDN_155291, prime_oneHundredTwentyDN_2655560587, prime_oneHundredTwentyDN_49146911386957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392084 : Nat.totient 141872026092338691301363392084 = 47263228657575396869984083104 := by
  rw [← show ((([(2, 2), (3, 1), (1723, 1), (6861676634375057617593509, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_1723, prime_oneHundredTwentyDN_6861676634375057617593509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392085 : Nat.totient 141872026092338691301363392085 = 109201518670050220997407319040 := by
  rw [← show ((([(5, 1), (53, 1), (59, 1), (431, 1), (8783, 1), (132763, 1), (18055173871829, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_53, prime_oneHundredTwentyDN_59, prime_oneHundredTwentyDN_431, prime_oneHundredTwentyDN_8783, prime_oneHundredTwentyDN_132763, prime_oneHundredTwentyDN_18055173871829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392086 : Nat.totient 141872026092338691301363392086 = 67047336507476945639929598208 := by
  rw [← show ((([(2, 1), (19, 1), (433, 1), (8622342657854545478386009, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_19, prime_oneHundredTwentyDN_433, prime_oneHundredTwentyDN_8622342657854545478386009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392087 : Nat.totient 141872026092338691301363392087 = 86422563906653520627097927680 := by
  rw [← show ((([(3, 2), (17, 2), (43, 1), (193, 1), (1213, 1), (34057, 1), (133723, 1), (1189754491, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_17, prime_oneHundredTwentyDN_43, prime_oneHundredTwentyDN_193, prime_oneHundredTwentyDN_1213, prime_oneHundredTwentyDN_34057, prime_oneHundredTwentyDN_133723, prime_oneHundredTwentyDN_1189754491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392088 : Nat.totient 141872026092338691301363392088 = 70684695575815380266709020160 := by
  rw [← show ((([(2, 3), (283, 1), (107071, 1), (11129533489, 1), (52586168543, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_283, prime_oneHundredTwentyDN_107071, prime_oneHundredTwentyDN_11129533489, prime_oneHundredTwentyDN_52586168543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392089 : Nat.totient 141872026092338691301363392089 = 137029363277300633178902016000 := by
  rw [← show ((([(41, 1), (109, 1), (1229, 1), (144511, 1), (413346319, 1), (432433721, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_41, prime_oneHundredTwentyDN_109, prime_oneHundredTwentyDN_1229, prime_oneHundredTwentyDN_144511, prime_oneHundredTwentyDN_413346319, prime_oneHundredTwentyDN_432433721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392090 : Nat.totient 141872026092338691301363392090 = 29312975282079373339779072000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (101, 1), (103, 1), (1163, 1), (3221, 1), (20357, 1), (53279, 1), (1229519, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_7, prime_oneHundredTwentyDN_13, prime_oneHundredTwentyDN_101, prime_oneHundredTwentyDN_103, prime_oneHundredTwentyDN_1163, prime_oneHundredTwentyDN_3221, prime_oneHundredTwentyDN_20357, prime_oneHundredTwentyDN_53279, prime_oneHundredTwentyDN_1229519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392091 : Nat.totient 141872026092338691301363392091 = 141868094267765004559925522032 := by
  rw [← show ((([(36083, 1), (3931824573686741437833977, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_36083, prime_oneHundredTwentyDN_3931824573686741437833977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392092 : Nat.totient 141872026092338691301363392092 = 70914664452293860526877605760 := by
  rw [← show ((([(2, 2), (3919, 1), (22003, 1), (2841961, 1), (144730980259499, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3919, prime_oneHundredTwentyDN_22003, prime_oneHundredTwentyDN_2841961, prime_oneHundredTwentyDN_144730980259499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392093 : Nat.totient 141872026092338691301363392093 = 85972659651095140549229760000 := by
  rw [← show ((([(3, 1), (11, 1), (8951, 1), (113621, 1), (3608377, 1), (1171495867063, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_11, prime_oneHundredTwentyDN_8951, prime_oneHundredTwentyDN_113621, prime_oneHundredTwentyDN_3608377, prime_oneHundredTwentyDN_1171495867063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392094 : Nat.totient 141872026092338691301363392094 = 70936013046164940467989988520 := by
  rw [← show ((([(2, 1), (16162151074357, 1), (4389020540633171, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_16162151074357, prime_oneHundredTwentyDN_4389020540633171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392095 : Nat.totient 141872026092338691301363392095 = 113493023141201014098584004864 := by
  rw [← show ((([(5, 1), (28793, 1), (173039, 1), (5695027857389254597, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_28793, prime_oneHundredTwentyDN_173039, prime_oneHundredTwentyDN_5695027857389254597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392096 : Nat.totient 141872026092338691301363392096 = 47281290125416518397188695040 := by
  rw [← show ((([(2, 5), (3, 2), (5879, 1), (35267, 1), (88812211, 1), (26752207429, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_5879, prime_oneHundredTwentyDN_35267, prime_oneHundredTwentyDN_88812211, prime_oneHundredTwentyDN_26752207429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392097 : Nat.totient 141872026092338691301363392097 = 121604593778922134008505200752 := by
  rw [← show ((([(7, 1), (8380149067, 1), (2418504985635183013, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_7, prime_oneHundredTwentyDN_8380149067, prime_oneHundredTwentyDN_2418504985635183013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392098 : Nat.totient 141872026092338691301363392098 = 70916204050624478477922496240 := by
  rw [← show ((([(2, 1), (3581, 1), (19808995544867172759196229, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_3581, prime_oneHundredTwentyDN_19808995544867172759196229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392099 : Nat.totient 141872026092338691301363392099 = 94579962688780337463629913600 := by
  rw [← show ((([(3, 1), (106433, 1), (189391, 1), (2346064108363272911, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_3, prime_oneHundredTwentyDN_106433, prime_oneHundredTwentyDN_189391, prime_oneHundredTwentyDN_2346064108363272911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392100 : Nat.totient 141872026092338691301363392100 = 53106131622140356638480138240 := by
  rw [← show ((([(2, 2), (5, 2), (23, 1), (47, 1), (2609, 1), (1030817, 1), (487995060087097, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_2, prime_oneHundredTwentyDN_5, prime_oneHundredTwentyDN_23, prime_oneHundredTwentyDN_47, prime_oneHundredTwentyDN_2609, prime_oneHundredTwentyDN_1030817, prime_oneHundredTwentyDN_487995060087097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyDN_141872026092338691301363392101 : Nat.totient 141872026092338691301363392101 = 141871065205723370037190580172 := by
  rw [← show ((([(147647, 1), (960886615321264172664283, 1)] : List FactorBlock).map factorBlockValue).prod) = 141872026092338691301363392101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyDN_147647, prime_oneHundredTwentyDN_960886615321264172664283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredTwentyDN : certifiedKill 1 141872026092338691301363391999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredTwentyDN_141872026092338691301363392000, phi_oneHundredTwentyDN_141872026092338691301363392001, phi_oneHundredTwentyDN_141872026092338691301363392002,
    phi_oneHundredTwentyDN_141872026092338691301363392003, phi_oneHundredTwentyDN_141872026092338691301363392004, phi_oneHundredTwentyDN_141872026092338691301363392005,
    phi_oneHundredTwentyDN_141872026092338691301363392006, phi_oneHundredTwentyDN_141872026092338691301363392007, phi_oneHundredTwentyDN_141872026092338691301363392008,
    phi_oneHundredTwentyDN_141872026092338691301363392009, phi_oneHundredTwentyDN_141872026092338691301363392010, phi_oneHundredTwentyDN_141872026092338691301363392011,
    phi_oneHundredTwentyDN_141872026092338691301363392012, phi_oneHundredTwentyDN_141872026092338691301363392013, phi_oneHundredTwentyDN_141872026092338691301363392014,
    phi_oneHundredTwentyDN_141872026092338691301363392015, phi_oneHundredTwentyDN_141872026092338691301363392016, phi_oneHundredTwentyDN_141872026092338691301363392017,
    phi_oneHundredTwentyDN_141872026092338691301363392018, phi_oneHundredTwentyDN_141872026092338691301363392019, phi_oneHundredTwentyDN_141872026092338691301363392020,
    phi_oneHundredTwentyDN_141872026092338691301363392021, phi_oneHundredTwentyDN_141872026092338691301363392022, phi_oneHundredTwentyDN_141872026092338691301363392023,
    phi_oneHundredTwentyDN_141872026092338691301363392024, phi_oneHundredTwentyDN_141872026092338691301363392025, phi_oneHundredTwentyDN_141872026092338691301363392026,
    phi_oneHundredTwentyDN_141872026092338691301363392027, phi_oneHundredTwentyDN_141872026092338691301363392028, phi_oneHundredTwentyDN_141872026092338691301363392029,
    phi_oneHundredTwentyDN_141872026092338691301363392030, phi_oneHundredTwentyDN_141872026092338691301363392031, phi_oneHundredTwentyDN_141872026092338691301363392032,
    phi_oneHundredTwentyDN_141872026092338691301363392033, phi_oneHundredTwentyDN_141872026092338691301363392034, phi_oneHundredTwentyDN_141872026092338691301363392035,
    phi_oneHundredTwentyDN_141872026092338691301363392036, phi_oneHundredTwentyDN_141872026092338691301363392037, phi_oneHundredTwentyDN_141872026092338691301363392038,
    phi_oneHundredTwentyDN_141872026092338691301363392039, phi_oneHundredTwentyDN_141872026092338691301363392040, phi_oneHundredTwentyDN_141872026092338691301363392041,
    phi_oneHundredTwentyDN_141872026092338691301363392042, phi_oneHundredTwentyDN_141872026092338691301363392043, phi_oneHundredTwentyDN_141872026092338691301363392044,
    phi_oneHundredTwentyDN_141872026092338691301363392045, phi_oneHundredTwentyDN_141872026092338691301363392046, phi_oneHundredTwentyDN_141872026092338691301363392047,
    phi_oneHundredTwentyDN_141872026092338691301363392048, phi_oneHundredTwentyDN_141872026092338691301363392049, phi_oneHundredTwentyDN_141872026092338691301363392050,
    phi_oneHundredTwentyDN_141872026092338691301363392051, phi_oneHundredTwentyDN_141872026092338691301363392052, phi_oneHundredTwentyDN_141872026092338691301363392053,
    phi_oneHundredTwentyDN_141872026092338691301363392054, phi_oneHundredTwentyDN_141872026092338691301363392055, phi_oneHundredTwentyDN_141872026092338691301363392056,
    phi_oneHundredTwentyDN_141872026092338691301363392057, phi_oneHundredTwentyDN_141872026092338691301363392058, phi_oneHundredTwentyDN_141872026092338691301363392059,
    phi_oneHundredTwentyDN_141872026092338691301363392060, phi_oneHundredTwentyDN_141872026092338691301363392061, phi_oneHundredTwentyDN_141872026092338691301363392062,
    phi_oneHundredTwentyDN_141872026092338691301363392063, phi_oneHundredTwentyDN_141872026092338691301363392064, phi_oneHundredTwentyDN_141872026092338691301363392065,
    phi_oneHundredTwentyDN_141872026092338691301363392066, phi_oneHundredTwentyDN_141872026092338691301363392067, phi_oneHundredTwentyDN_141872026092338691301363392068,
    phi_oneHundredTwentyDN_141872026092338691301363392069, phi_oneHundredTwentyDN_141872026092338691301363392070, phi_oneHundredTwentyDN_141872026092338691301363392071,
    phi_oneHundredTwentyDN_141872026092338691301363392072, phi_oneHundredTwentyDN_141872026092338691301363392073, phi_oneHundredTwentyDN_141872026092338691301363392074,
    phi_oneHundredTwentyDN_141872026092338691301363392075, phi_oneHundredTwentyDN_141872026092338691301363392076, phi_oneHundredTwentyDN_141872026092338691301363392077,
    phi_oneHundredTwentyDN_141872026092338691301363392078, phi_oneHundredTwentyDN_141872026092338691301363392079, phi_oneHundredTwentyDN_141872026092338691301363392080,
    phi_oneHundredTwentyDN_141872026092338691301363392081, phi_oneHundredTwentyDN_141872026092338691301363392082, phi_oneHundredTwentyDN_141872026092338691301363392083,
    phi_oneHundredTwentyDN_141872026092338691301363392084, phi_oneHundredTwentyDN_141872026092338691301363392085, phi_oneHundredTwentyDN_141872026092338691301363392086,
    phi_oneHundredTwentyDN_141872026092338691301363392087, phi_oneHundredTwentyDN_141872026092338691301363392088, phi_oneHundredTwentyDN_141872026092338691301363392089,
    phi_oneHundredTwentyDN_141872026092338691301363392090, phi_oneHundredTwentyDN_141872026092338691301363392091, phi_oneHundredTwentyDN_141872026092338691301363392092,
    phi_oneHundredTwentyDN_141872026092338691301363392093, phi_oneHundredTwentyDN_141872026092338691301363392094, phi_oneHundredTwentyDN_141872026092338691301363392095,
    phi_oneHundredTwentyDN_141872026092338691301363392096, phi_oneHundredTwentyDN_141872026092338691301363392097, phi_oneHundredTwentyDN_141872026092338691301363392098,
    phi_oneHundredTwentyDN_141872026092338691301363392099, phi_oneHundredTwentyDN_141872026092338691301363392100, phi_oneHundredTwentyDN_141872026092338691301363392101
    ]

end TotientTailPeriodKiller
end Erdos249257
