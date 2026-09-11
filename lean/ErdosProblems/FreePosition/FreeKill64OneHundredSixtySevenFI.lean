import Erdos249257.DiagonalPincerCertificatesT64
/- Kernel-checked off-diagonal certificate at a freely chosen position. -/
namespace Erdos249257
namespace TotientTailPeriodKiller
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
private def oneHundredSixtySevenFIFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredSixtySevenFIFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredSixtySevenFIFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredSixtySevenFIFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredSixtySevenFIFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredSixtySevenFIFastPow a n * oneHundredSixtySevenFIFastPow a n * a else oneHundredSixtySevenFIFastPow a n * oneHundredSixtySevenFIFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredSixtySevenFI_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredSixtySevenFI_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredSixtySevenFI_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredSixtySevenFI_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredSixtySevenFI_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredSixtySevenFI_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredSixtySevenFI_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredSixtySevenFI_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredSixtySevenFI_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredSixtySevenFI_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredSixtySevenFI_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredSixtySevenFI_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredSixtySevenFI_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredSixtySevenFI_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredSixtySevenFI_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredSixtySevenFI_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredSixtySevenFI_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredSixtySevenFI_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredSixtySevenFI_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredSixtySevenFI_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredSixtySevenFI_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredSixtySevenFI_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredSixtySevenFI_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredSixtySevenFI_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredSixtySevenFI_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredSixtySevenFI_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredSixtySevenFI_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredSixtySevenFI_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredSixtySevenFI_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredSixtySevenFI_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredSixtySevenFI_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredSixtySevenFI_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredSixtySevenFI_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredSixtySevenFI_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredSixtySevenFI_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredSixtySevenFI_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredSixtySevenFI_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredSixtySevenFI_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredSixtySevenFI_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredSixtySevenFI_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredSixtySevenFI_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredSixtySevenFI_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredSixtySevenFI_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredSixtySevenFI_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredSixtySevenFI_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredSixtySevenFI_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredSixtySevenFI_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredSixtySevenFI_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredSixtySevenFI_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredSixtySevenFI_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredSixtySevenFI_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredSixtySevenFI_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredSixtySevenFI_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredSixtySevenFI_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredSixtySevenFI_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredSixtySevenFI_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredSixtySevenFI_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredSixtySevenFI_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredSixtySevenFI_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredSixtySevenFI_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredSixtySevenFI_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredSixtySevenFI_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredSixtySevenFI_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredSixtySevenFI_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredSixtySevenFI_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredSixtySevenFI_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredSixtySevenFI_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredSixtySevenFI_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredSixtySevenFI_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredSixtySevenFI_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredSixtySevenFI_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredSixtySevenFI_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredSixtySevenFI_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredSixtySevenFI_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredSixtySevenFI_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredSixtySevenFI_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredSixtySevenFI_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredSixtySevenFI_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredSixtySevenFI_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredSixtySevenFI_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredSixtySevenFI_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredSixtySevenFI_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredSixtySevenFI_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredSixtySevenFI_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredSixtySevenFI_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredSixtySevenFI_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredSixtySevenFI_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredSixtySevenFI_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredSixtySevenFI_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredSixtySevenFI_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredSixtySevenFI_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredSixtySevenFI_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredSixtySevenFI_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredSixtySevenFI_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredSixtySevenFI_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredSixtySevenFI_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredSixtySevenFI_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredSixtySevenFI_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredSixtySevenFI_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredSixtySevenFI_863 : Nat.Prime 863 := by norm_num

private theorem prime_oneHundredSixtySevenFI_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredSixtySevenFI_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredSixtySevenFI_953 : Nat.Prime 953 := by norm_num

private theorem prime_oneHundredSixtySevenFI_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredSixtySevenFI_983 : Nat.Prime 983 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1373 : Nat.Prime 1373 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1381 : Nat.Prime 1381 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1423 : Nat.Prime 1423 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1429 : Nat.Prime 1429 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1433 : Nat.Prime 1433 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1471 : Nat.Prime 1471 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1483 : Nat.Prime 1483 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1601 : Nat.Prime 1601 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1663 : Nat.Prime 1663 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1699 : Nat.Prime 1699 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1787 : Nat.Prime 1787 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1867 : Nat.Prime 1867 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2029 : Nat.Prime 2029 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2039 : Nat.Prime 2039 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2111 : Nat.Prime 2111 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2213 : Nat.Prime 2213 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2251 : Nat.Prime 2251 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2297 : Nat.Prime 2297 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2309 : Nat.Prime 2309 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2311 : Nat.Prime 2311 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2377 : Nat.Prime 2377 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2399 : Nat.Prime 2399 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2417 : Nat.Prime 2417 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2473 : Nat.Prime 2473 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2621 : Nat.Prime 2621 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2647 : Nat.Prime 2647 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2659 : Nat.Prime 2659 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2729 : Nat.Prime 2729 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2753 : Nat.Prime 2753 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2833 : Nat.Prime 2833 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2851 : Nat.Prime 2851 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3019 : Nat.Prime 3019 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3163 : Nat.Prime 3163 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3169 : Nat.Prime 3169 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3229 : Nat.Prime 3229 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3299 : Nat.Prime 3299 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3319 : Nat.Prime 3319 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3343 : Nat.Prime 3343 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3361 : Nat.Prime 3361 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3413 : Nat.Prime 3413 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3449 : Nat.Prime 3449 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3467 : Nat.Prime 3467 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3517 : Nat.Prime 3517 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3583 : Nat.Prime 3583 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3739 : Nat.Prime 3739 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3943 : Nat.Prime 3943 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3947 : Nat.Prime 3947 := by norm_num

private theorem prime_oneHundredSixtySevenFI_4019 : Nat.Prime 4019 := by norm_num

private theorem prime_oneHundredSixtySevenFI_4049 : Nat.Prime 4049 := by norm_num

private theorem prime_oneHundredSixtySevenFI_4111 : Nat.Prime 4111 := by norm_num

private theorem prime_oneHundredSixtySevenFI_4339 : Nat.Prime 4339 := by norm_num

private theorem prime_oneHundredSixtySevenFI_4457 : Nat.Prime 4457 := by norm_num

private theorem prime_oneHundredSixtySevenFI_4523 : Nat.Prime 4523 := by norm_num

private theorem prime_oneHundredSixtySevenFI_5209 : Nat.Prime 5209 := by norm_num

private theorem prime_oneHundredSixtySevenFI_5281 : Nat.Prime 5281 := by norm_num

private theorem prime_oneHundredSixtySevenFI_5387 : Nat.Prime 5387 := by norm_num

private theorem prime_oneHundredSixtySevenFI_5393 : Nat.Prime 5393 := by norm_num

private theorem prime_oneHundredSixtySevenFI_5653 : Nat.Prime 5653 := by norm_num

private theorem prime_oneHundredSixtySevenFI_5743 : Nat.Prime 5743 := by norm_num

private theorem prime_oneHundredSixtySevenFI_5791 : Nat.Prime 5791 := by norm_num

private theorem prime_oneHundredSixtySevenFI_6257 : Nat.Prime 6257 := by norm_num

private theorem prime_oneHundredSixtySevenFI_6581 : Nat.Prime 6581 := by norm_num

private theorem prime_oneHundredSixtySevenFI_6967 : Nat.Prime 6967 := by norm_num

private theorem prime_oneHundredSixtySevenFI_7057 : Nat.Prime 7057 := by norm_num

private theorem prime_oneHundredSixtySevenFI_7253 : Nat.Prime 7253 := by norm_num

private theorem prime_oneHundredSixtySevenFI_7283 : Nat.Prime 7283 := by norm_num

private theorem prime_oneHundredSixtySevenFI_7307 : Nat.Prime 7307 := by norm_num

private theorem prime_oneHundredSixtySevenFI_7523 : Nat.Prime 7523 := by norm_num

private theorem prime_oneHundredSixtySevenFI_7547 : Nat.Prime 7547 := by norm_num

private theorem prime_oneHundredSixtySevenFI_7573 : Nat.Prime 7573 := by norm_num

private theorem prime_oneHundredSixtySevenFI_7883 : Nat.Prime 7883 := by norm_num

private theorem prime_oneHundredSixtySevenFI_8009 : Nat.Prime 8009 := by norm_num

private theorem prime_oneHundredSixtySevenFI_8089 : Nat.Prime 8089 := by norm_num

private theorem prime_oneHundredSixtySevenFI_8297 : Nat.Prime 8297 := by norm_num

private theorem prime_oneHundredSixtySevenFI_8311 : Nat.Prime 8311 := by norm_num

private theorem prime_oneHundredSixtySevenFI_8521 : Nat.Prime 8521 := by norm_num

private theorem prime_oneHundredSixtySevenFI_8731 : Nat.Prime 8731 := by norm_num

private theorem prime_oneHundredSixtySevenFI_9151 : Nat.Prime 9151 := by norm_num

private theorem prime_oneHundredSixtySevenFI_9473 : Nat.Prime 9473 := by norm_num

private theorem prime_oneHundredSixtySevenFI_9739 : Nat.Prime 9739 := by norm_num

private theorem prime_oneHundredSixtySevenFI_10099 : Nat.Prime 10099 := by norm_num

private theorem prime_oneHundredSixtySevenFI_10303 : Nat.Prime 10303 := by norm_num

private theorem prime_oneHundredSixtySevenFI_10369 : Nat.Prime 10369 := by norm_num

private theorem prime_oneHundredSixtySevenFI_10627 : Nat.Prime 10627 := by norm_num

private theorem prime_oneHundredSixtySevenFI_11279 : Nat.Prime 11279 := by norm_num

private theorem prime_oneHundredSixtySevenFI_11489 : Nat.Prime 11489 := by norm_num

private theorem prime_oneHundredSixtySevenFI_11887 : Nat.Prime 11887 := by norm_num

private theorem prime_oneHundredSixtySevenFI_12113 : Nat.Prime 12113 := by norm_num

private theorem prime_oneHundredSixtySevenFI_12641 : Nat.Prime 12641 := by norm_num

private theorem prime_oneHundredSixtySevenFI_13033 : Nat.Prime 13033 := by norm_num

private theorem prime_oneHundredSixtySevenFI_13103 : Nat.Prime 13103 := by norm_num

private theorem prime_oneHundredSixtySevenFI_13669 : Nat.Prime 13669 := by norm_num

private theorem prime_oneHundredSixtySevenFI_13933 : Nat.Prime 13933 := by norm_num

private theorem prime_oneHundredSixtySevenFI_13967 : Nat.Prime 13967 := by norm_num

private theorem prime_oneHundredSixtySevenFI_14009 : Nat.Prime 14009 := by norm_num

private theorem prime_oneHundredSixtySevenFI_14011 : Nat.Prime 14011 := by norm_num

private theorem prime_oneHundredSixtySevenFI_14071 : Nat.Prime 14071 := by norm_num

private theorem prime_oneHundredSixtySevenFI_14537 : Nat.Prime 14537 := by norm_num

private theorem prime_oneHundredSixtySevenFI_14827 : Nat.Prime 14827 := by norm_num

private theorem prime_oneHundredSixtySevenFI_16811 : Nat.Prime 16811 := by norm_num

private theorem prime_oneHundredSixtySevenFI_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredSixtySevenFI_17923 : Nat.Prime 17923 := by norm_num

private theorem prime_oneHundredSixtySevenFI_18127 : Nat.Prime 18127 := by norm_num

private theorem prime_oneHundredSixtySevenFI_18253 : Nat.Prime 18253 := by norm_num

private theorem prime_oneHundredSixtySevenFI_18521 : Nat.Prime 18521 := by norm_num

private theorem prime_oneHundredSixtySevenFI_18523 : Nat.Prime 18523 := by norm_num

private theorem prime_oneHundredSixtySevenFI_18911 : Nat.Prime 18911 := by norm_num

private theorem prime_oneHundredSixtySevenFI_19139 : Nat.Prime 19139 := by norm_num

private theorem prime_oneHundredSixtySevenFI_19213 : Nat.Prime 19213 := by norm_num

private theorem prime_oneHundredSixtySevenFI_19391 : Nat.Prime 19391 := by norm_num

private theorem prime_oneHundredSixtySevenFI_20333 : Nat.Prime 20333 := by norm_num

private theorem prime_oneHundredSixtySevenFI_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredSixtySevenFI_21059 : Nat.Prime 21059 := by norm_num

private theorem prime_oneHundredSixtySevenFI_21193 : Nat.Prime 21193 := by norm_num

private theorem prime_oneHundredSixtySevenFI_23549 : Nat.Prime 23549 := by norm_num

private theorem prime_oneHundredSixtySevenFI_24317 : Nat.Prime 24317 := by norm_num

private theorem prime_oneHundredSixtySevenFI_24593 : Nat.Prime 24593 := by norm_num

private theorem prime_oneHundredSixtySevenFI_25163 : Nat.Prime 25163 := by norm_num

private theorem prime_oneHundredSixtySevenFI_25579 : Nat.Prime 25579 := by norm_num

private theorem prime_oneHundredSixtySevenFI_27241 : Nat.Prime 27241 := by norm_num

private theorem prime_oneHundredSixtySevenFI_27259 : Nat.Prime 27259 := by norm_num

private theorem prime_oneHundredSixtySevenFI_29411 : Nat.Prime 29411 := by norm_num

private theorem prime_oneHundredSixtySevenFI_30703 : Nat.Prime 30703 := by norm_num

private theorem prime_oneHundredSixtySevenFI_31147 : Nat.Prime 31147 := by norm_num

private theorem prime_oneHundredSixtySevenFI_31477 : Nat.Prime 31477 := by norm_num

private theorem prime_oneHundredSixtySevenFI_32467 : Nat.Prime 32467 := by norm_num

private theorem prime_oneHundredSixtySevenFI_32569 : Nat.Prime 32569 := by norm_num

private theorem prime_oneHundredSixtySevenFI_33773 : Nat.Prime 33773 := by norm_num

private theorem prime_oneHundredSixtySevenFI_34679 : Nat.Prime 34679 := by norm_num

private theorem prime_oneHundredSixtySevenFI_36469 : Nat.Prime 36469 := by norm_num

private theorem prime_oneHundredSixtySevenFI_37123 : Nat.Prime 37123 := by norm_num

private theorem prime_oneHundredSixtySevenFI_40823 : Nat.Prime 40823 := by norm_num

private theorem prime_oneHundredSixtySevenFI_42821 : Nat.Prime 42821 := by norm_num

private theorem prime_oneHundredSixtySevenFI_43787 : Nat.Prime 43787 := by norm_num

private theorem prime_oneHundredSixtySevenFI_44053 : Nat.Prime 44053 := by norm_num

private theorem prime_oneHundredSixtySevenFI_45887 : Nat.Prime 45887 := by norm_num

private theorem prime_oneHundredSixtySevenFI_49057 : Nat.Prime 49057 := by norm_num

private theorem prime_oneHundredSixtySevenFI_53069 : Nat.Prime 53069 := by norm_num

private theorem prime_oneHundredSixtySevenFI_53951 : Nat.Prime 53951 := by norm_num

private theorem prime_oneHundredSixtySevenFI_57977 : Nat.Prime 57977 := by norm_num

private theorem prime_oneHundredSixtySevenFI_57991 : Nat.Prime 57991 := by norm_num

private theorem prime_oneHundredSixtySevenFI_63113 : Nat.Prime 63113 := by norm_num

private theorem prime_oneHundredSixtySevenFI_68171 : Nat.Prime 68171 := by norm_num

private theorem prime_oneHundredSixtySevenFI_69239 : Nat.Prime 69239 := by norm_num

private theorem prime_oneHundredSixtySevenFI_69877 : Nat.Prime 69877 := by norm_num

private theorem prime_oneHundredSixtySevenFI_70849 : Nat.Prime 70849 := by norm_num

private theorem prime_oneHundredSixtySevenFI_70999 : Nat.Prime 70999 := by norm_num

private theorem prime_oneHundredSixtySevenFI_71443 : Nat.Prime 71443 := by norm_num

private theorem prime_oneHundredSixtySevenFI_72461 : Nat.Prime 72461 := by norm_num

private theorem prime_oneHundredSixtySevenFI_74377 : Nat.Prime 74377 := by norm_num

private theorem prime_oneHundredSixtySevenFI_76733 : Nat.Prime 76733 := by norm_num

private theorem prime_oneHundredSixtySevenFI_79103 : Nat.Prime 79103 := by norm_num

private theorem prime_oneHundredSixtySevenFI_81817 : Nat.Prime 81817 := by norm_num

private theorem prime_oneHundredSixtySevenFI_83003 : Nat.Prime 83003 := by norm_num

private theorem prime_oneHundredSixtySevenFI_90373 : Nat.Prime 90373 := by norm_num

private theorem prime_oneHundredSixtySevenFI_90583 : Nat.Prime 90583 := by norm_num

private theorem prime_oneHundredSixtySevenFI_93893 : Nat.Prime 93893 := by norm_num

private theorem prime_oneHundredSixtySevenFI_100669 : Nat.Prime 100669 := by norm_num

private theorem prime_oneHundredSixtySevenFI_101051 : Nat.Prime 101051 := by norm_num

private theorem prime_oneHundredSixtySevenFI_101483 : Nat.Prime 101483 := by norm_num

private theorem prime_oneHundredSixtySevenFI_102019 : Nat.Prime 102019 := by norm_num

private theorem prime_oneHundredSixtySevenFI_110251 : Nat.Prime 110251 := by norm_num

private theorem prime_oneHundredSixtySevenFI_115001 : Nat.Prime 115001 := by norm_num

private theorem prime_oneHundredSixtySevenFI_115321 : Nat.Prime 115321 := by norm_num

private theorem prime_oneHundredSixtySevenFI_122029 : Nat.Prime 122029 := by norm_num

private theorem prime_oneHundredSixtySevenFI_133279 : Nat.Prime 133279 := by norm_num

private theorem prime_oneHundredSixtySevenFI_135029 : Nat.Prime 135029 := by norm_num

private theorem prime_oneHundredSixtySevenFI_136483 : Nat.Prime 136483 := by norm_num

private theorem prime_oneHundredSixtySevenFI_137867 : Nat.Prime 137867 := by norm_num

private theorem prime_oneHundredSixtySevenFI_138563 : Nat.Prime 138563 := by norm_num

private theorem prime_oneHundredSixtySevenFI_139901 : Nat.Prime 139901 := by norm_num

private theorem prime_oneHundredSixtySevenFI_144037 : Nat.Prime 144037 := by norm_num

private theorem prime_oneHundredSixtySevenFI_145037 : Nat.Prime 145037 := by norm_num

private theorem prime_oneHundredSixtySevenFI_147229 : Nat.Prime 147229 := by norm_num

private theorem prime_oneHundredSixtySevenFI_165559 : Nat.Prime 165559 := by norm_num

private theorem prime_oneHundredSixtySevenFI_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredSixtySevenFI_173291 : Nat.Prime 173291 := by norm_num

private theorem prime_oneHundredSixtySevenFI_182549 : Nat.Prime 182549 := by norm_num

private theorem prime_oneHundredSixtySevenFI_211643 : Nat.Prime 211643 := by norm_num

private theorem prime_oneHundredSixtySevenFI_218809 : Nat.Prime 218809 := by norm_num

private theorem prime_oneHundredSixtySevenFI_231299 : Nat.Prime 231299 := by norm_num

private theorem prime_oneHundredSixtySevenFI_253871 : Nat.Prime 253871 := by norm_num

private theorem prime_oneHundredSixtySevenFI_262597 : Nat.Prime 262597 := by norm_num

private theorem prime_oneHundredSixtySevenFI_269623 : Nat.Prime 269623 := by norm_num

private theorem prime_oneHundredSixtySevenFI_292069 : Nat.Prime 292069 := by norm_num

private theorem prime_oneHundredSixtySevenFI_293107 : Nat.Prime 293107 := by norm_num

private theorem prime_oneHundredSixtySevenFI_295259 : Nat.Prime 295259 := by norm_num

private theorem prime_oneHundredSixtySevenFI_300151 : Nat.Prime 300151 := by norm_num

private theorem prime_oneHundredSixtySevenFI_307171 : Nat.Prime 307171 := by norm_num

private theorem prime_oneHundredSixtySevenFI_316507 : Nat.Prime 316507 := by norm_num

private theorem prime_oneHundredSixtySevenFI_327809 : Nat.Prime 327809 := by norm_num

private theorem prime_oneHundredSixtySevenFI_331241 : Nat.Prime 331241 := by norm_num

private theorem prime_oneHundredSixtySevenFI_352481 : Nat.Prime 352481 := by norm_num

private theorem prime_oneHundredSixtySevenFI_359621 : Nat.Prime 359621 := by norm_num

private theorem prime_oneHundredSixtySevenFI_361217 : Nat.Prime 361217 := by norm_num

private theorem prime_oneHundredSixtySevenFI_362137 : Nat.Prime 362137 := by norm_num

private theorem prime_oneHundredSixtySevenFI_362911 : Nat.Prime 362911 := by norm_num

private theorem prime_oneHundredSixtySevenFI_365293 : Nat.Prime 365293 := by norm_num

private theorem prime_oneHundredSixtySevenFI_367819 : Nat.Prime 367819 := by norm_num

private theorem prime_oneHundredSixtySevenFI_395741 : Nat.Prime 395741 := by norm_num

private theorem prime_oneHundredSixtySevenFI_407501 : Nat.Prime 407501 := by norm_num

private theorem prime_oneHundredSixtySevenFI_427069 : Nat.Prime 427069 := by norm_num

private theorem prime_oneHundredSixtySevenFI_434479 : Nat.Prime 434479 := by norm_num

private theorem prime_oneHundredSixtySevenFI_461257 : Nat.Prime 461257 := by norm_num

private theorem prime_oneHundredSixtySevenFI_475697 : Nat.Prime 475697 := by norm_num

private theorem prime_oneHundredSixtySevenFI_483317 : Nat.Prime 483317 := by norm_num

private theorem prime_oneHundredSixtySevenFI_503147 : Nat.Prime 503147 := by norm_num

private theorem prime_oneHundredSixtySevenFI_531551 : Nat.Prime 531551 := by norm_num

private theorem prime_oneHundredSixtySevenFI_557269 : Nat.Prime 557269 := by norm_num

private theorem prime_oneHundredSixtySevenFI_564653 : Nat.Prime 564653 := by norm_num

private theorem prime_oneHundredSixtySevenFI_569251 : Nat.Prime 569251 := by norm_num

private theorem prime_oneHundredSixtySevenFI_579779 : Nat.Prime 579779 := by norm_num

private theorem prime_oneHundredSixtySevenFI_586139 : Nat.Prime 586139 := by norm_num

private theorem prime_oneHundredSixtySevenFI_604249 : Nat.Prime 604249 := by norm_num

private theorem prime_oneHundredSixtySevenFI_619391 : Nat.Prime 619391 := by norm_num

private theorem prime_oneHundredSixtySevenFI_622129 : Nat.Prime 622129 := by norm_num

private theorem prime_oneHundredSixtySevenFI_638699 : Nat.Prime 638699 := by norm_num

private theorem prime_oneHundredSixtySevenFI_648677 : Nat.Prime 648677 := by norm_num

private theorem prime_oneHundredSixtySevenFI_649709 : Nat.Prime 649709 := by norm_num

private theorem prime_oneHundredSixtySevenFI_669863 : Nat.Prime 669863 := by norm_num

private theorem prime_oneHundredSixtySevenFI_790523 : Nat.Prime 790523 := by norm_num

private theorem prime_oneHundredSixtySevenFI_801407 : Nat.Prime 801407 := by norm_num

private theorem prime_oneHundredSixtySevenFI_802297 : Nat.Prime 802297 := by norm_num

private theorem prime_oneHundredSixtySevenFI_834131 : Nat.Prime 834131 := by norm_num

private theorem prime_oneHundredSixtySevenFI_865069 : Nat.Prime 865069 := by norm_num

private theorem prime_oneHundredSixtySevenFI_876433 : Nat.Prime 876433 := by norm_num

private theorem prime_oneHundredSixtySevenFI_893723 : Nat.Prime 893723 := by norm_num

private theorem prime_oneHundredSixtySevenFI_929953 : Nat.Prime 929953 := by norm_num

private theorem prime_oneHundredSixtySevenFI_934229 : Nat.Prime 934229 := by norm_num

private theorem prime_oneHundredSixtySevenFI_950527 : Nat.Prime 950527 := by norm_num

private theorem prime_oneHundredSixtySevenFI_986593 : Nat.Prime 986593 := by norm_num

private theorem prime_oneHundredSixtySevenFI_988129 : Nat.Prime 988129 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1007647 : Nat.Prime 1007647 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1090613 : Nat.Prime 1090613 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1096427 : Nat.Prime 1096427 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1135951 : Nat.Prime 1135951 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1175969 : Nat.Prime 1175969 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1232797 : Nat.Prime 1232797 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1361029 : Nat.Prime 1361029 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1690219 : Nat.Prime 1690219 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1699793 : Nat.Prime 1699793 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1705493 : Nat.Prime 1705493 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1712531 : Nat.Prime 1712531 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1880839 : Nat.Prime 1880839 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1886471 : Nat.Prime 1886471 := by norm_num

private theorem prime_oneHundredSixtySevenFI_1899589 : Nat.Prime 1899589 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2073251 : Nat.Prime 2073251 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2162813 : Nat.Prime 2162813 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2163221 : Nat.Prime 2163221 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2210291 : Nat.Prime 2210291 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2361133 : Nat.Prime 2361133 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2372563 : Nat.Prime 2372563 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2508307 : Nat.Prime 2508307 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2547689 : Nat.Prime 2547689 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2571721 : Nat.Prime 2571721 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2704199 : Nat.Prime 2704199 := by norm_num

private theorem prime_oneHundredSixtySevenFI_2710997 : Nat.Prime 2710997 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3079697 : Nat.Prime 3079697 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3113633 : Nat.Prime 3113633 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3187733 : Nat.Prime 3187733 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3192047 : Nat.Prime 3192047 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3364987 : Nat.Prime 3364987 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3476503 : Nat.Prime 3476503 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3526993 : Nat.Prime 3526993 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3709117 : Nat.Prime 3709117 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3872731 : Nat.Prime 3872731 := by norm_num

private theorem prime_oneHundredSixtySevenFI_3915941 : Nat.Prime 3915941 := by norm_num

private theorem prime_oneHundredSixtySevenFI_4166303 : Nat.Prime 4166303 := by norm_num

private theorem prime_oneHundredSixtySevenFI_4182611 : Nat.Prime 4182611 := by norm_num

private theorem prime_oneHundredSixtySevenFI_4244497 : Nat.Prime 4244497 := by norm_num

private theorem prime_oneHundredSixtySevenFI_4281649 : Nat.Prime 4281649 := by norm_num

private theorem prime_oneHundredSixtySevenFI_4419589 : Nat.Prime 4419589 := by norm_num

private theorem prime_oneHundredSixtySevenFI_4656721 : Nat.Prime 4656721 := by norm_num

private theorem prime_oneHundredSixtySevenFI_5120183 : Nat.Prime 5120183 := by norm_num

private theorem prime_oneHundredSixtySevenFI_5482039 : Nat.Prime 5482039 := by norm_num

private theorem prime_oneHundredSixtySevenFI_5577199 : Nat.Prime 5577199 := by norm_num

private theorem prime_oneHundredSixtySevenFI_5952911 : Nat.Prime 5952911 := by norm_num

private theorem prime_oneHundredSixtySevenFI_6215431 : Nat.Prime 6215431 := by norm_num

private theorem prime_oneHundredSixtySevenFI_6321683 : Nat.Prime 6321683 := by norm_num

private theorem prime_oneHundredSixtySevenFI_6712129 : Nat.Prime 6712129 := by norm_num

private theorem prime_oneHundredSixtySevenFI_6714217 : Nat.Prime 6714217 := by norm_num

private theorem prime_oneHundredSixtySevenFI_6788147 : Nat.Prime 6788147 := by norm_num

private theorem prime_oneHundredSixtySevenFI_7030561 : Nat.Prime 7030561 := by norm_num

private theorem prime_oneHundredSixtySevenFI_7122149 : Nat.Prime 7122149 := by norm_num

private theorem prime_oneHundredSixtySevenFI_7124443 : Nat.Prime 7124443 := by norm_num

private theorem prime_oneHundredSixtySevenFI_7287733 : Nat.Prime 7287733 := by norm_num

private theorem prime_oneHundredSixtySevenFI_7644079 : Nat.Prime 7644079 := by norm_num

private theorem prime_oneHundredSixtySevenFI_7974919 : Nat.Prime 7974919 := by norm_num

private theorem prime_oneHundredSixtySevenFI_8081123 : Nat.Prime 8081123 := by norm_num

private theorem prime_oneHundredSixtySevenFI_9168853 : Nat.Prime 9168853 := by norm_num

private theorem prime_oneHundredSixtySevenFI_9999929 : Nat.Prime 9999929 := by norm_num

private theorem prime_oneHundredSixtySevenFI_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredSixtySevenFI_11285507 : Nat.Prime 11285507 := by norm_num

private theorem prime_oneHundredSixtySevenFI_11370613 : Nat.Prime 11370613 := by norm_num

private theorem prime_oneHundredSixtySevenFI_11632141 : Nat.Prime 11632141 := by norm_num

private theorem prime_oneHundredSixtySevenFI_11808583 : Nat.Prime 11808583 := by norm_num

private theorem prime_oneHundredSixtySevenFI_13888003 : Nat.Prime 13888003 := by norm_num

private theorem prime_oneHundredSixtySevenFI_14193043 : Nat.Prime 14193043 := by norm_num

private theorem prime_oneHundredSixtySevenFI_14368567 : Nat.Prime 14368567 := by norm_num

private theorem prime_oneHundredSixtySevenFI_15095117 : Nat.Prime 15095117 := by norm_num

private theorem prime_oneHundredSixtySevenFI_15145693 : Nat.Prime 15145693 := by norm_num

private theorem prime_oneHundredSixtySevenFI_15861817 : Nat.Prime 15861817 := by norm_num

private theorem prime_oneHundredSixtySevenFI_15939433 : Nat.Prime 15939433 := by norm_num

private theorem prime_oneHundredSixtySevenFI_16926253 : Nat.Prime 16926253 := by norm_num

private theorem prime_oneHundredSixtySevenFI_18072289 : Nat.Prime 18072289 := by norm_num

private theorem prime_oneHundredSixtySevenFI_18473633 : Nat.Prime 18473633 := by norm_num

private theorem prime_oneHundredSixtySevenFI_21014069 : Nat.Prime 21014069 := by norm_num

private theorem prime_oneHundredSixtySevenFI_21190123 : Nat.Prime 21190123 := by norm_num

private theorem prime_oneHundredSixtySevenFI_21239707 : Nat.Prime 21239707 := by norm_num

private theorem prime_oneHundredSixtySevenFI_22368691 : Nat.Prime 22368691 := by norm_num

private theorem prime_oneHundredSixtySevenFI_22523299 : Nat.Prime 22523299 := by norm_num

private theorem prime_oneHundredSixtySevenFI_24008363 : Nat.Prime 24008363 := by norm_num

private theorem prime_oneHundredSixtySevenFI_27230057 : Nat.Prime 27230057 := by norm_num

private theorem prime_oneHundredSixtySevenFI_28437653 : Nat.Prime 28437653 := by norm_num

private theorem prime_oneHundredSixtySevenFI_32059609 : Nat.Prime 32059609 := by
  apply lucas_primality 32059609 (17 : ZMod 32059609)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (23, 1), (8297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (23, 1), (8297, 1)] : List FactorBlock).map factorBlockValue).prod) = 32059609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_23
      · exact prime_oneHundredSixtySevenFI_8297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 32059609) ^ 16029804 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (17 : ZMod 32059609) ^ 10686536 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (17 : ZMod 32059609) ^ 4579944 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (17 : ZMod 32059609) ^ 1393896 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (17 : ZMod 32059609) ^ 3864 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_35261909 : Nat.Prime 35261909 := by
  apply lucas_primality 35261909 (3 : ZMod 35261909)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (801407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (801407, 1)] : List FactorBlock).map factorBlockValue).prod) = 35261909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_801407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 35261909) ^ 17630954 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 35261909) ^ 3205628 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 35261909) ^ 44 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_35637227 : Nat.Prime 35637227 := by
  apply lucas_primality 35637227 (2 : ZMod 35637227)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1499, 1), (11887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1499, 1), (11887, 1)] : List FactorBlock).map factorBlockValue).prod) = 35637227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_1499
      · exact prime_oneHundredSixtySevenFI_11887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35637227) ^ 17818613 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 35637227) ^ 23774 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 35637227) ^ 2998 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_36860771 : Nat.Prime 36860771 := by
  apply lucas_primality 36860771 (6 : ZMod 36860771)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (199, 1), (18523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (199, 1), (18523, 1)] : List FactorBlock).map factorBlockValue).prod) = 36860771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_199
      · exact prime_oneHundredSixtySevenFI_18523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 36860771) ^ 18430385 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 36860771) ^ 7372154 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 36860771) ^ 185230 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 36860771) ^ 1990 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_37198121 : Nat.Prime 37198121 := by
  apply lucas_primality 37198121 (6 : ZMod 37198121)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (929953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (929953, 1)] : List FactorBlock).map factorBlockValue).prod) = 37198121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_929953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 37198121) ^ 18599060 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 37198121) ^ 7439624 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 37198121) ^ 40 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_37292587 : Nat.Prime 37292587 := by
  apply lucas_primality 37292587 (5 : ZMod 37292587)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6215431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6215431, 1)] : List FactorBlock).map factorBlockValue).prod) = 37292587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_6215431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 37292587) ^ 18646293 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 37292587) ^ 12430862 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 37292587) ^ 6 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_39201719 : Nat.Prime 39201719 := by
  apply lucas_primality 39201719 (7 : ZMod 39201719)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3413, 1), (5743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3413, 1), (5743, 1)] : List FactorBlock).map factorBlockValue).prod) = 39201719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3413
      · exact prime_oneHundredSixtySevenFI_5743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 39201719) ^ 19600859 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 39201719) ^ 11486 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 39201719) ^ 6826 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_41106077 : Nat.Prime 41106077 := by
  apply lucas_primality 41106077 (3 : ZMod 41106077)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (934229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (934229, 1)] : List FactorBlock).map factorBlockValue).prod) = 41106077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_934229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 41106077) ^ 20553038 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 41106077) ^ 3736916 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 41106077) ^ 44 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_43765499 : Nat.Prime 43765499 := by
  apply lucas_primality 43765499 (2 : ZMod 43765499)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1181, 1), (2647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1181, 1), (2647, 1)] : List FactorBlock).map factorBlockValue).prod) = 43765499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_1181
      · exact prime_oneHundredSixtySevenFI_2647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43765499) ^ 21882749 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 43765499) ^ 6252214 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 43765499) ^ 37058 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 43765499) ^ 16534 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_44110037 : Nat.Prime 44110037 := by
  apply lucas_primality 44110037 (2 : ZMod 44110037)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (648677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (648677, 1)] : List FactorBlock).map factorBlockValue).prod) = 44110037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_17
      · exact prime_oneHundredSixtySevenFI_648677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 44110037) ^ 22055018 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 44110037) ^ 2594708 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 44110037) ^ 68 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_45482453 : Nat.Prime 45482453 := by
  apply lucas_primality 45482453 (2 : ZMod 45482453)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11370613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11370613, 1)] : List FactorBlock).map factorBlockValue).prod) = 45482453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_11370613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 45482453) ^ 22741226 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 45482453) ^ 4 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_45496111 : Nat.Prime 45496111 := by
  apply lucas_primality 45496111 (6 : ZMod 45496111)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (137867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (137867, 1)] : List FactorBlock).map factorBlockValue).prod) = 45496111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_137867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45496111) ^ 22748055 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 45496111) ^ 15165370 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 45496111) ^ 9099222 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 45496111) ^ 4136010 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 45496111) ^ 330 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_45718843 : Nat.Prime 45718843 := by
  apply lucas_primality 45718843 (3 : ZMod 45718843)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (586139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (586139, 1)] : List FactorBlock).map factorBlockValue).prod) = 45718843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_586139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45718843) ^ 22859421 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 45718843) ^ 15239614 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 45718843) ^ 3516834 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 45718843) ^ 78 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_52072289 : Nat.Prime 52072289 := by
  apply lucas_primality 52072289 (3 : ZMod 52072289)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (53, 1), (30703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (53, 1), (30703, 1)] : List FactorBlock).map factorBlockValue).prod) = 52072289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_53
      · exact prime_oneHundredSixtySevenFI_30703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 52072289) ^ 26036144 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 52072289) ^ 982496 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 52072289) ^ 1696 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_55694209 : Nat.Prime 55694209 := by
  apply lucas_primality 55694209 (11 : ZMod 55694209)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (145037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (145037, 1)] : List FactorBlock).map factorBlockValue).prod) = 55694209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_145037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 55694209) ^ 27847104 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 55694209) ^ 18564736 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 55694209) ^ 384 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_67705013 : Nat.Prime 67705013 := by
  apply lucas_primality 67705013 (2 : ZMod 67705013)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (16926253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (16926253, 1)] : List FactorBlock).map factorBlockValue).prod) = 67705013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_16926253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 67705013) ^ 33852506 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 67705013) ^ 4 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_67713043 : Nat.Prime 67713043 := by
  apply lucas_primality 67713043 (2 : ZMod 67713043)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11285507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11285507, 1)] : List FactorBlock).map factorBlockValue).prod) = 67713043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11285507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 67713043) ^ 33856521 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 67713043) ^ 22571014 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 67713043) ^ 6 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_69107681 : Nat.Prime 69107681 := by
  apply lucas_primality 69107681 (3 : ZMod 69107681)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (31, 1), (13933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (31, 1), (13933, 1)] : List FactorBlock).map factorBlockValue).prod) = 69107681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_31
      · exact prime_oneHundredSixtySevenFI_13933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 69107681) ^ 34553840 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 69107681) ^ 13821536 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 69107681) ^ 2229280 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 69107681) ^ 4960 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_73915367 : Nat.Prime 73915367 := by
  apply lucas_primality 73915367 (5 : ZMod 73915367)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (43, 1), (199, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (43, 1), (199, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) = 73915367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_43
      · exact prime_oneHundredSixtySevenFI_199
      · exact prime_oneHundredSixtySevenFI_617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 73915367) ^ 36957683 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 73915367) ^ 10559338 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 73915367) ^ 1718962 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 73915367) ^ 371434 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 73915367) ^ 119798 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_74396243 : Nat.Prime 74396243 := by
  apply lucas_primality 74396243 (2 : ZMod 74396243)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37198121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37198121, 1)] : List FactorBlock).map factorBlockValue).prod) = 74396243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_37198121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 74396243) ^ 37198121 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 74396243) ^ 2 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_88628563 : Nat.Prime 88628563 := by
  apply lucas_primality 88628563 (2 : ZMod 88628563)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (83, 1), (5393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (83, 1), (5393, 1)] : List FactorBlock).map factorBlockValue).prod) = 88628563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_83
      · exact prime_oneHundredSixtySevenFI_5393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 88628563) ^ 44314281 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 88628563) ^ 29542854 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 88628563) ^ 8057142 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 88628563) ^ 1067814 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 88628563) ^ 16434 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_98576461 : Nat.Prime 98576461 := by
  apply lucas_primality 98576461 (10 : ZMod 98576461)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (182549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (182549, 1)] : List FactorBlock).map factorBlockValue).prod) = 98576461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_182549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 98576461) ^ 49288230 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 98576461) ^ 32858820 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 98576461) ^ 19715292 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 98576461) ^ 540 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_120986809 : Nat.Prime 120986809 := by
  apply lucas_primality 120986809 (7 : ZMod 120986809)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (149, 1), (1471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (149, 1), (1471, 1)] : List FactorBlock).map factorBlockValue).prod) = 120986809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_23
      · exact prime_oneHundredSixtySevenFI_149
      · exact prime_oneHundredSixtySevenFI_1471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 120986809) ^ 60493404 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 120986809) ^ 40328936 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 120986809) ^ 5260296 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 120986809) ^ 811992 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 120986809) ^ 82248 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_124329883 : Nat.Prime 124329883 := by
  apply lucas_primality 124329883 (2 : ZMod 124329883)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (1090613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (1090613, 1)] : List FactorBlock).map factorBlockValue).prod) = 124329883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_1090613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 124329883) ^ 62164941 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 124329883) ^ 41443294 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 124329883) ^ 6543678 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 124329883) ^ 114 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_140670643 : Nat.Prime 140670643 := by
  apply lucas_primality 140670643 (2 : ZMod 140670643)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (409, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (409, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) = 140670643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_409
      · exact prime_oneHundredSixtySevenFI_431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 140670643) ^ 70335321 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 140670643) ^ 46890214 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 140670643) ^ 20095806 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 140670643) ^ 7403718 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 140670643) ^ 343938 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 140670643) ^ 326382 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_146322529 : Nat.Prime 146322529 := by
  apply lucas_primality 146322529 (7 : ZMod 146322529)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (138563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (138563, 1)] : List FactorBlock).map factorBlockValue).prod) = 146322529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_138563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 146322529) ^ 73161264 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 146322529) ^ 48774176 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 146322529) ^ 13302048 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 146322529) ^ 1056 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_148792487 : Nat.Prime 148792487 := by
  apply lucas_primality 148792487 (5 : ZMod 148792487)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (74396243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (74396243, 1)] : List FactorBlock).map factorBlockValue).prod) = 148792487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_74396243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 148792487) ^ 74396243 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 148792487) ^ 2 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_149682557 : Nat.Prime 149682557 := by
  apply lucas_primality 149682557 (2 : ZMod 149682557)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (211, 1), (2647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (211, 1), (2647, 1)] : List FactorBlock).map factorBlockValue).prod) = 149682557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_67
      · exact prime_oneHundredSixtySevenFI_211
      · exact prime_oneHundredSixtySevenFI_2647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 149682557) ^ 74841278 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 149682557) ^ 2234068 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 149682557) ^ 709396 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 149682557) ^ 56548 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_155681651 : Nat.Prime 155681651 := by
  apply lucas_primality 155681651 (2 : ZMod 155681651)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (3113633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (3113633, 1)] : List FactorBlock).map factorBlockValue).prod) = 155681651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_3113633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 155681651) ^ 77840825 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 155681651) ^ 31136330 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 155681651) ^ 50 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_160590403 : Nat.Prime 160590403 := by
  apply lucas_primality 160590403 (3 : ZMod 160590403)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (113, 1), (11279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (113, 1), (11279, 1)] : List FactorBlock).map factorBlockValue).prod) = 160590403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_113
      · exact prime_oneHundredSixtySevenFI_11279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 160590403) ^ 80295201 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 160590403) ^ 53530134 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 160590403) ^ 22941486 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 160590403) ^ 1421154 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 160590403) ^ 14238 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_178887827 : Nat.Prime 178887827 := by
  apply lucas_primality 178887827 (2 : ZMod 178887827)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (43, 1), (53, 1), (3019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (43, 1), (53, 1), (3019, 1)] : List FactorBlock).map factorBlockValue).prod) = 178887827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_43
      · exact prime_oneHundredSixtySevenFI_53
      · exact prime_oneHundredSixtySevenFI_3019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 178887827) ^ 89443913 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 178887827) ^ 13760602 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 178887827) ^ 4160182 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 178887827) ^ 3375242 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 178887827) ^ 59254 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_182875373 : Nat.Prime 182875373 := by
  apply lucas_primality 182875373 (2 : ZMod 182875373)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (45718843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (45718843, 1)] : List FactorBlock).map factorBlockValue).prod) = 182875373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_45718843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 182875373) ^ 91437686 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 182875373) ^ 4 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_188891089 : Nat.Prime 188891089 := by
  apply lucas_primality 188891089 (22 : ZMod 188891089)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 2), (43, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 2), (43, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) = 188891089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_23
      · exact prime_oneHundredSixtySevenFI_43
      · exact prime_oneHundredSixtySevenFI_173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 188891089) ^ 94445544 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (22 : ZMod 188891089) ^ 62963696 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (22 : ZMod 188891089) ^ 8212656 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (22 : ZMod 188891089) ^ 4392816 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (22 : ZMod 188891089) ^ 1091856 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_190457623 : Nat.Prime 190457623 := by
  apply lucas_primality 190457623 (3 : ZMod 190457623)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (3526993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (3526993, 1)] : List FactorBlock).map factorBlockValue).prod) = 190457623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_3526993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 190457623) ^ 95228811 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 190457623) ^ 63485874 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 190457623) ^ 54 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_220140317 : Nat.Prime 220140317 := by
  apply lucas_primality 220140317 (2 : ZMod 220140317)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (41, 1), (122029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (41, 1), (122029, 1)] : List FactorBlock).map factorBlockValue).prod) = 220140317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_41
      · exact prime_oneHundredSixtySevenFI_122029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 220140317) ^ 110070158 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 220140317) ^ 20012756 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 220140317) ^ 5369276 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 220140317) ^ 1804 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_242660701 : Nat.Prime 242660701 := by
  apply lucas_primality 242660701 (10 : ZMod 242660701)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (269623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (269623, 1)] : List FactorBlock).map factorBlockValue).prod) = 242660701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_269623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 242660701) ^ 121330350 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 242660701) ^ 80886900 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 242660701) ^ 48532140 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 242660701) ^ 900 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_244373293 : Nat.Prime 244373293 := by
  apply lucas_primality 244373293 (5 : ZMod 244373293)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (6788147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (6788147, 1)] : List FactorBlock).map factorBlockValue).prod) = 244373293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_6788147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 244373293) ^ 122186646 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 244373293) ^ 81457764 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 244373293) ^ 36 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_252480271 : Nat.Prime 252480271 := by
  apply lucas_primality 252480271 (7 : ZMod 252480271)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (839, 1), (1433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (839, 1), (1433, 1)] : List FactorBlock).map factorBlockValue).prod) = 252480271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_839
      · exact prime_oneHundredSixtySevenFI_1433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 252480271) ^ 126240135 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 252480271) ^ 84160090 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 252480271) ^ 50496054 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 252480271) ^ 36068610 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 252480271) ^ 300930 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 252480271) ^ 176190 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_282095273 : Nat.Prime 282095273 := by
  apply lucas_primality 282095273 (3 : ZMod 282095273)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (35261909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (35261909, 1)] : List FactorBlock).map factorBlockValue).prod) = 282095273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_35261909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 282095273) ^ 141047636 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 282095273) ^ 8 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_309570839 : Nat.Prime 309570839 := by
  apply lucas_primality 309570839 (7 : ZMod 309570839)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (151, 1), (53951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (151, 1), (53951, 1)] : List FactorBlock).map factorBlockValue).prod) = 309570839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_151
      · exact prime_oneHundredSixtySevenFI_53951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 309570839) ^ 154785419 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 309570839) ^ 16293202 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 309570839) ^ 2050138 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 309570839) ^ 5738 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_311892697 : Nat.Prime 311892697 := by
  apply lucas_primality 311892697 (15 : ZMod 311892697)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (23, 1), (127, 1), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (23, 1), (127, 1), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) = 311892697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_23
      · exact prime_oneHundredSixtySevenFI_127
      · exact prime_oneHundredSixtySevenFI_1483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 311892697) ^ 155946348 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (15 : ZMod 311892697) ^ 103964232 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (15 : ZMod 311892697) ^ 13560552 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (15 : ZMod 311892697) ^ 2455848 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (15 : ZMod 311892697) ^ 210312 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_316962509 : Nat.Prime 316962509 := by
  apply lucas_primality 316962509 (2 : ZMod 316962509)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3739, 1), (21193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3739, 1), (21193, 1)] : List FactorBlock).map factorBlockValue).prod) = 316962509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3739
      · exact prime_oneHundredSixtySevenFI_21193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 316962509) ^ 158481254 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 316962509) ^ 84772 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 316962509) ^ 14956 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_351654091 : Nat.Prime 351654091 := by
  apply lucas_primality 351654091 (2 : ZMod 351654091)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (587, 1), (1051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (587, 1), (1051, 1)] : List FactorBlock).map factorBlockValue).prod) = 351654091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_587
      · exact prime_oneHundredSixtySevenFI_1051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 351654091) ^ 175827045 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 351654091) ^ 117218030 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 351654091) ^ 70330818 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 351654091) ^ 18508110 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 351654091) ^ 599070 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 351654091) ^ 334590 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_368631691 : Nat.Prime 368631691 := by
  apply lucas_primality 368631691 (3 : ZMod 368631691)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (43, 1), (40823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (43, 1), (40823, 1)] : List FactorBlock).map factorBlockValue).prod) = 368631691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_43
      · exact prime_oneHundredSixtySevenFI_40823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 368631691) ^ 184315845 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 368631691) ^ 122877230 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 368631691) ^ 73726338 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 368631691) ^ 52661670 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 368631691) ^ 8572830 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 368631691) ^ 9030 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_382044709 : Nat.Prime 382044709 := by
  apply lucas_primality 382044709 (2 : ZMod 382044709)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (61, 1), (57991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (61, 1), (57991, 1)] : List FactorBlock).map factorBlockValue).prod) = 382044709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_61
      · exact prime_oneHundredSixtySevenFI_57991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 382044709) ^ 191022354 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 382044709) ^ 127348236 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 382044709) ^ 6263028 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 382044709) ^ 6588 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_426582223 : Nat.Prime 426582223 := by
  apply lucas_primality 426582223 (3 : ZMod 426582223)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1429, 1), (4523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1429, 1), (4523, 1)] : List FactorBlock).map factorBlockValue).prod) = 426582223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_1429
      · exact prime_oneHundredSixtySevenFI_4523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 426582223) ^ 213291111 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 426582223) ^ 142194074 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 426582223) ^ 38780202 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 426582223) ^ 298518 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 426582223) ^ 94314 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_497319533 : Nat.Prime 497319533 := by
  apply lucas_primality 497319533 (2 : ZMod 497319533)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (124329883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (124329883, 1)] : List FactorBlock).map factorBlockValue).prod) = 497319533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_124329883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 497319533) ^ 248659766 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 497319533) ^ 4 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_525185989 : Nat.Prime 525185989 := by
  apply lucas_primality 525185989 (2 : ZMod 525185989)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43765499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43765499, 1)] : List FactorBlock).map factorBlockValue).prod) = 525185989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_43765499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 525185989) ^ 262592994 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 525185989) ^ 175061996 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 525185989) ^ 12 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_585576791 : Nat.Prime 585576791 := by
  apply lucas_primality 585576791 (7 : ZMod 585576791)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (101, 1), (579779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (101, 1), (579779, 1)] : List FactorBlock).map factorBlockValue).prod) = 585576791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_101
      · exact prime_oneHundredSixtySevenFI_579779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 585576791) ^ 292788395 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 585576791) ^ 117115358 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 585576791) ^ 5797790 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 585576791) ^ 1010 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_605307119 : Nat.Prime 605307119 := by
  apply lucas_primality 605307119 (7 : ZMod 605307119)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (3299, 1), (7057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (3299, 1), (7057, 1)] : List FactorBlock).map factorBlockValue).prod) = 605307119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_3299
      · exact prime_oneHundredSixtySevenFI_7057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 605307119) ^ 302653559 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 605307119) ^ 46562086 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 605307119) ^ 183482 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 605307119) ^ 85774 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_642361613 : Nat.Prime 642361613 := by
  apply lucas_primality 642361613 (2 : ZMod 642361613)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (160590403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (160590403, 1)] : List FactorBlock).map factorBlockValue).prod) = 642361613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_160590403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 642361613) ^ 321180806 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 642361613) ^ 4 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_17203
      · exact prime_oneHundredSixtySevenFI_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_742084921 : Nat.Prime 742084921 := by
  apply lucas_primality 742084921 (11 : ZMod 742084921)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (79, 1), (97, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (79, 1), (97, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) = 742084921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_79
      · exact prime_oneHundredSixtySevenFI_97
      · exact prime_oneHundredSixtySevenFI_269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 742084921) ^ 371042460 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 742084921) ^ 247361640 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 742084921) ^ 148416984 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 742084921) ^ 9393480 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 742084921) ^ 7650360 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 742084921) ^ 2758680 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_818929999 : Nat.Prime 818929999 := by
  apply lucas_primality 818929999 (6 : ZMod 818929999)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (45496111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (45496111, 1)] : List FactorBlock).map factorBlockValue).prod) = 818929999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_45496111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 818929999) ^ 409464999 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 818929999) ^ 272976666 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 818929999) ^ 18 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_824848799 : Nat.Prime 824848799 := by
  apply lucas_primality 824848799 (11 : ZMod 824848799)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (157, 1), (90583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (157, 1), (90583, 1)] : List FactorBlock).map factorBlockValue).prod) = 824848799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_29
      · exact prime_oneHundredSixtySevenFI_157
      · exact prime_oneHundredSixtySevenFI_90583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 824848799) ^ 412424399 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 824848799) ^ 28443062 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 824848799) ^ 5253814 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 824848799) ^ 9106 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_940426477 : Nat.Prime 940426477 := by
  apply lucas_primality 940426477 (5 : ZMod 940426477)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (7124443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (7124443, 1)] : List FactorBlock).map factorBlockValue).prod) = 940426477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_7124443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 940426477) ^ 470213238 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 940426477) ^ 313475492 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 940426477) ^ 85493316 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 940426477) ^ 132 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_995633021 : Nat.Prime 995633021 := by
  apply lucas_primality 995633021 (2 : ZMod 995633021)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (103, 1), (483317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (103, 1), (483317, 1)] : List FactorBlock).map factorBlockValue).prod) = 995633021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_103
      · exact prime_oneHundredSixtySevenFI_483317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 995633021) ^ 497816510 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 995633021) ^ 199126604 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 995633021) ^ 9666340 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 995633021) ^ 2060 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_999051533 : Nat.Prime 999051533 := by
  apply lucas_primality 999051533 (2 : ZMod 999051533)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (2210291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (2210291, 1)] : List FactorBlock).map factorBlockValue).prod) = 999051533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_113
      · exact prime_oneHundredSixtySevenFI_2210291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 999051533) ^ 499525766 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 999051533) ^ 8841164 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 999051533) ^ 452 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1176799123 : Nat.Prime 1176799123 := by
  apply lucas_primality 1176799123 (3 : ZMod 1176799123)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (67, 1), (31477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (67, 1), (31477, 1)] : List FactorBlock).map factorBlockValue).prod) = 1176799123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_31
      · exact prime_oneHundredSixtySevenFI_67
      · exact prime_oneHundredSixtySevenFI_31477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1176799123) ^ 588399561 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1176799123) ^ 392266374 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1176799123) ^ 37961262 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1176799123) ^ 17564166 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1176799123) ^ 37386 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1284723227 : Nat.Prime 1284723227 := by
  apply lucas_primality 1284723227 (2 : ZMod 1284723227)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (642361613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (642361613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1284723227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_642361613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1284723227) ^ 642361613 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1284723227) ^ 2 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1338400181 : Nat.Prime 1338400181 := by
  apply lucas_primality 1338400181 (2 : ZMod 1338400181)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (97, 1), (53069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (97, 1), (53069, 1)] : List FactorBlock).map factorBlockValue).prod) = 1338400181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_97
      · exact prime_oneHundredSixtySevenFI_53069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1338400181) ^ 669200090 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1338400181) ^ 267680036 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1338400181) ^ 102953860 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1338400181) ^ 13797940 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1338400181) ^ 25220 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1481221003 : Nat.Prime 1481221003 := by
  apply lucas_primality 1481221003 (34 : ZMod 1481221003)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (443, 1), (557269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (443, 1), (557269, 1)] : List FactorBlock).map factorBlockValue).prod) = 1481221003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_443
      · exact prime_oneHundredSixtySevenFI_557269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (34 : ZMod 1481221003) ^ 740610501 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (34 : ZMod 1481221003) ^ 493740334 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (34 : ZMod 1481221003) ^ 3343614 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (34 : ZMod 1481221003) ^ 2658 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1604959859 : Nat.Prime 1604959859 := by
  apply lucas_primality 1604959859 (2 : ZMod 1604959859)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (631, 1), (1103, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (631, 1), (1103, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) = 1604959859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_631
      · exact prime_oneHundredSixtySevenFI_1103
      · exact prime_oneHundredSixtySevenFI_1153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1604959859) ^ 802479929 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1604959859) ^ 2543518 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1604959859) ^ 1455086 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1604959859) ^ 1391986 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1978746983 : Nat.Prime 1978746983 := by
  apply lucas_primality 1978746983 (5 : ZMod 1978746983)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (52072289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (52072289, 1)] : List FactorBlock).map factorBlockValue).prod) = 1978746983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_52072289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1978746983) ^ 989373491 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1978746983) ^ 104144578 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1978746983) ^ 38 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1998103067 : Nat.Prime 1998103067 := by
  apply lucas_primality 1998103067 (2 : ZMod 1998103067)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (999051533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (999051533, 1)] : List FactorBlock).map factorBlockValue).prod) = 1998103067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_999051533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1998103067) ^ 999051533 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1998103067) ^ 2 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_2391538579 : Nat.Prime 2391538579 := by
  apply lucas_primality 2391538579 (2 : ZMod 2391538579)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (1601, 1), (1741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (1601, 1), (1741, 1)] : List FactorBlock).map factorBlockValue).prod) = 2391538579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_1601
      · exact prime_oneHundredSixtySevenFI_1741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2391538579) ^ 1195769289 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2391538579) ^ 797179526 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2391538579) ^ 217412598 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2391538579) ^ 183964506 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2391538579) ^ 1493778 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2391538579) ^ 1373658 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_2535700073 : Nat.Prime 2535700073 := by
  apply lucas_primality 2535700073 (3 : ZMod 2535700073)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (316962509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (316962509, 1)] : List FactorBlock).map factorBlockValue).prod) = 2535700073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_316962509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2535700073) ^ 1267850036 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2535700073) ^ 8 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_3463081249 : Nat.Prime 3463081249 := by
  apply lucas_primality 3463081249 (7 : ZMod 3463081249)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (1367, 1), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (1367, 1), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) = 3463081249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_1367
      · exact prime_oneHundredSixtySevenFI_2399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3463081249) ^ 1731540624 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 3463081249) ^ 1154360416 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 3463081249) ^ 314825568 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 3463081249) ^ 2533344 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 3463081249) ^ 1443552 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_3730113601 : Nat.Prime 3730113601 := by
  apply lucas_primality 3730113601 (26 : ZMod 3730113601)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (383, 1), (2029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (383, 1), (2029, 1)] : List FactorBlock).map factorBlockValue).prod) = 3730113601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_383
      · exact prime_oneHundredSixtySevenFI_2029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 3730113601) ^ 1865056800 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (26 : ZMod 3730113601) ^ 1243371200 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (26 : ZMod 3730113601) ^ 746022720 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (26 : ZMod 3730113601) ^ 9739200 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (26 : ZMod 3730113601) ^ 1838400 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_4097030813 : Nat.Prime 4097030813 := by
  apply lucas_primality 4097030813 (2 : ZMod 4097030813)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (146322529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (146322529, 1)] : List FactorBlock).map factorBlockValue).prod) = 4097030813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_146322529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4097030813) ^ 2048515406 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4097030813) ^ 585290116 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4097030813) ^ 28 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_4942916129 : Nat.Prime 4942916129 := by
  apply lucas_primality 4942916129 (3 : ZMod 4942916129)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (307, 1), (503147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (307, 1), (503147, 1)] : List FactorBlock).map factorBlockValue).prod) = 4942916129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_307
      · exact prime_oneHundredSixtySevenFI_503147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4942916129) ^ 2471458064 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4942916129) ^ 16100704 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4942916129) ^ 9824 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_5118777541 : Nat.Prime 5118777541 := by
  apply lucas_primality 5118777541 (2 : ZMod 5118777541)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (28437653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (28437653, 1)] : List FactorBlock).map factorBlockValue).prod) = 5118777541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_28437653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5118777541) ^ 2559388770 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5118777541) ^ 1706259180 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5118777541) ^ 1023755508 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5118777541) ^ 180 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_5487287497 : Nat.Prime 5487287497 := by
  apply lucas_primality 5487287497 (5 : ZMod 5487287497)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1381, 1), (165559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1381, 1), (165559, 1)] : List FactorBlock).map factorBlockValue).prod) = 5487287497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_1381
      · exact prime_oneHundredSixtySevenFI_165559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5487287497) ^ 2743643748 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5487287497) ^ 1829095832 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5487287497) ^ 3973416 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5487287497) ^ 33144 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_5551358353 : Nat.Prime 5551358353 := by
  apply lucas_primality 5551358353 (5 : ZMod 5551358353)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1049, 1), (110251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1049, 1), (110251, 1)] : List FactorBlock).map factorBlockValue).prod) = 5551358353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_1049
      · exact prime_oneHundredSixtySevenFI_110251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5551358353) ^ 2775679176 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5551358353) ^ 1850452784 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5551358353) ^ 5292048 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5551358353) ^ 50352 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_31
      · exact prime_oneHundredSixtySevenFI_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_6278187029 : Nat.Prime 6278187029 := by
  apply lucas_primality 6278187029 (2 : ZMod 6278187029)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (2039, 1), (11489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (2039, 1), (11489, 1)] : List FactorBlock).map factorBlockValue).prod) = 6278187029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_67
      · exact prime_oneHundredSixtySevenFI_2039
      · exact prime_oneHundredSixtySevenFI_11489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6278187029) ^ 3139093514 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6278187029) ^ 93704284 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6278187029) ^ 3079052 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6278187029) ^ 546452 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_7351635589 : Nat.Prime 7351635589 := by
  apply lucas_primality 7351635589 (2 : ZMod 7351635589)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (55694209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (55694209, 1)] : List FactorBlock).map factorBlockValue).prod) = 7351635589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_55694209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7351635589) ^ 3675817794 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7351635589) ^ 2450545196 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7351635589) ^ 668330508 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7351635589) ^ 132 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_7708339363 : Nat.Prime 7708339363 := by
  apply lucas_primality 7708339363 (5 : ZMod 7708339363)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1284723227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1284723227, 1)] : List FactorBlock).map factorBlockValue).prod) = 7708339363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_1284723227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7708339363) ^ 3854169681 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7708339363) ^ 2569446454 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7708339363) ^ 6 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_8637170023 : Nat.Prime 8637170023 := by
  apply lucas_primality 8637170023 (3 : ZMod 8637170023)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (71, 1), (173291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (71, 1), (173291, 1)] : List FactorBlock).map factorBlockValue).prod) = 8637170023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_71
      · exact prime_oneHundredSixtySevenFI_173291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8637170023) ^ 4318585011 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8637170023) ^ 2879056674 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8637170023) ^ 664397694 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8637170023) ^ 121650282 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8637170023) ^ 49842 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_8807497463 : Nat.Prime 8807497463 := by
  apply lucas_primality 8807497463 (5 : ZMod 8807497463)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 1), (59, 1), (67, 1), (3449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 1), (59, 1), (67, 1), (3449, 1)] : List FactorBlock).map factorBlockValue).prod) = 8807497463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_17
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_59
      · exact prime_oneHundredSixtySevenFI_67
      · exact prime_oneHundredSixtySevenFI_3449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8807497463) ^ 4403748731 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 8807497463) ^ 518088086 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 8807497463) ^ 463552498 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 8807497463) ^ 149279618 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 8807497463) ^ 131455186 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 8807497463) ^ 2553638 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_9824885093 : Nat.Prime 9824885093 := by
  apply lucas_primality 9824885093 (2 : ZMod 9824885093)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (67, 1), (107, 1), (31147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (67, 1), (107, 1), (31147, 1)] : List FactorBlock).map factorBlockValue).prod) = 9824885093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_67
      · exact prime_oneHundredSixtySevenFI_107
      · exact prime_oneHundredSixtySevenFI_31147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9824885093) ^ 4912442546 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9824885093) ^ 893171372 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9824885093) ^ 146640076 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9824885093) ^ 91821356 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9824885093) ^ 315436 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_9898185589 : Nat.Prime 9898185589 := by
  apply lucas_primality 9898185589 (2 : ZMod 9898185589)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (824848799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (824848799, 1)] : List FactorBlock).map factorBlockValue).prod) = 9898185589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_824848799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9898185589) ^ 4949092794 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9898185589) ^ 3299395196 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9898185589) ^ 12 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_10242004921 : Nat.Prime 10242004921 := by
  apply lucas_primality 10242004921 (13 : ZMod 10242004921)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (61, 1), (137, 1), (1459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (61, 1), (137, 1), (1459, 1)] : List FactorBlock).map factorBlockValue).prod) = 10242004921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_61
      · exact prime_oneHundredSixtySevenFI_137
      · exact prime_oneHundredSixtySevenFI_1459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 10242004921) ^ 5121002460 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 10242004921) ^ 3414001640 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 10242004921) ^ 2048400984 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 10242004921) ^ 1463143560 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 10242004921) ^ 167901720 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 10242004921) ^ 74759160 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 10242004921) ^ 7019880 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_10585233983 : Nat.Prime 10585233983 := by
  apply lucas_primality 10585233983 (5 : ZMod 10585233983)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (461, 1), (604249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (461, 1), (604249, 1)] : List FactorBlock).map factorBlockValue).prod) = 10585233983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_461
      · exact prime_oneHundredSixtySevenFI_604249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10585233983) ^ 5292616991 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 10585233983) ^ 557117578 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 10585233983) ^ 22961462 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 10585233983) ^ 17518 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_10757236097 : Nat.Prime 10757236097 := by
  apply lucas_primality 10757236097 (3 : ZMod 10757236097)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (31, 1), (2710997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (31, 1), (2710997, 1)] : List FactorBlock).map factorBlockValue).prod) = 10757236097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_31
      · exact prime_oneHundredSixtySevenFI_2710997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 10757236097) ^ 5378618048 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 10757236097) ^ 347007616 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 10757236097) ^ 3968 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_11351498399 : Nat.Prime 11351498399 := by
  apply lucas_primality 11351498399 (13 : ZMod 11351498399)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (229, 1), (669863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (229, 1), (669863, 1)] : List FactorBlock).map factorBlockValue).prod) = 11351498399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_37
      · exact prime_oneHundredSixtySevenFI_229
      · exact prime_oneHundredSixtySevenFI_669863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 11351498399) ^ 5675749199 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 11351498399) ^ 306797254 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 11351498399) ^ 49569862 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 11351498399) ^ 16946 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_11593973059 : Nat.Prime 11593973059 := by
  apply lucas_primality 11593973059 (2 : ZMod 11593973059)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (3947, 1), (7307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (3947, 1), (7307, 1)] : List FactorBlock).map factorBlockValue).prod) = 11593973059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_67
      · exact prime_oneHundredSixtySevenFI_3947
      · exact prime_oneHundredSixtySevenFI_7307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11593973059) ^ 5796986529 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11593973059) ^ 3864657686 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11593973059) ^ 173044374 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11593973059) ^ 2937414 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11593973059) ^ 1586694 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_12657976939 : Nat.Prime 12657976939 := by
  apply lucas_primality 12657976939 (2 : ZMod 12657976939)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (59, 1), (709, 1), (16811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (59, 1), (709, 1), (16811, 1)] : List FactorBlock).map factorBlockValue).prod) = 12657976939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_59
      · exact prime_oneHundredSixtySevenFI_709
      · exact prime_oneHundredSixtySevenFI_16811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12657976939) ^ 6328988469 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 12657976939) ^ 4219325646 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 12657976939) ^ 214541982 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 12657976939) ^ 17853282 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 12657976939) ^ 752958 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_12872462117 : Nat.Prime 12872462117 := by
  apply lucas_primality 12872462117 (3 : ZMod 12872462117)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (59, 1), (1880839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (59, 1), (1880839, 1)] : List FactorBlock).map factorBlockValue).prod) = 12872462117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_29
      · exact prime_oneHundredSixtySevenFI_59
      · exact prime_oneHundredSixtySevenFI_1880839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12872462117) ^ 6436231058 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 12872462117) ^ 443878004 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 12872462117) ^ 218177324 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 12872462117) ^ 6844 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_13954151899 : Nat.Prime 13954151899 := by
  apply lucas_primality 13954151899 (7 : ZMod 13954151899)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (139, 1), (5577199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (139, 1), (5577199, 1)] : List FactorBlock).map factorBlockValue).prod) = 13954151899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_139
      · exact prime_oneHundredSixtySevenFI_5577199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 13954151899) ^ 6977075949 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 13954151899) ^ 4651383966 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 13954151899) ^ 100389582 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 13954151899) ^ 2502 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_14377470097 : Nat.Prime 14377470097 := by
  apply lucas_primality 14377470097 (10 : ZMod 14377470097)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (27230057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (27230057, 1)] : List FactorBlock).map factorBlockValue).prod) = 14377470097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_27230057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 14377470097) ^ 7188735048 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 14377470097) ^ 4792490032 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 14377470097) ^ 1307042736 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 14377470097) ^ 528 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_15316376849 : Nat.Prime 15316376849 := by
  apply lucas_primality 15316376849 (3 : ZMod 15316376849)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (4019, 1), (14011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (4019, 1), (14011, 1)] : List FactorBlock).map factorBlockValue).prod) = 15316376849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_17
      · exact prime_oneHundredSixtySevenFI_4019
      · exact prime_oneHundredSixtySevenFI_14011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 15316376849) ^ 7658188424 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15316376849) ^ 900963344 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15316376849) ^ 3810992 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15316376849) ^ 1093168 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_15539889667 : Nat.Prime 15539889667 := by
  apply lucas_primality 15539889667 (3 : ZMod 15539889667)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (9999929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (9999929, 1)] : List FactorBlock).map factorBlockValue).prod) = 15539889667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_37
      · exact prime_oneHundredSixtySevenFI_9999929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15539889667) ^ 7769944833 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15539889667) ^ 5179963222 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15539889667) ^ 2219984238 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15539889667) ^ 419997018 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15539889667) ^ 1554 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_20989512977 : Nat.Prime 20989512977 := by
  apply lucas_primality 20989512977 (3 : ZMod 20989512977)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (523, 1), (2508307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (523, 1), (2508307, 1)] : List FactorBlock).map factorBlockValue).prod) = 20989512977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_523
      · exact prime_oneHundredSixtySevenFI_2508307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20989512977) ^ 10494756488 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 20989512977) ^ 40132912 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 20989512977) ^ 8368 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_22699715923 : Nat.Prime 22699715923 := by
  apply lucas_primality 22699715923 (2 : ZMod 22699715923)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (1423, 1), (68171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (1423, 1), (68171, 1)] : List FactorBlock).map factorBlockValue).prod) = 22699715923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_1423
      · exact prime_oneHundredSixtySevenFI_68171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22699715923) ^ 11349857961 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 22699715923) ^ 7566571974 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 22699715923) ^ 1746131994 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 22699715923) ^ 15952014 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 22699715923) ^ 332982 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_23812745533 : Nat.Prime 23812745533 := by
  apply lucas_primality 23812745533 (2 : ZMod 23812745533)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (449, 1), (4419589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (449, 1), (4419589, 1)] : List FactorBlock).map factorBlockValue).prod) = 23812745533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_449
      · exact prime_oneHundredSixtySevenFI_4419589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23812745533) ^ 11906372766 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 23812745533) ^ 7937581844 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 23812745533) ^ 53035068 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 23812745533) ^ 5388 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_25194668663 : Nat.Prime 25194668663 := by
  apply lucas_primality 25194668663 (5 : ZMod 25194668663)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (457, 1), (950527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (457, 1), (950527, 1)] : List FactorBlock).map factorBlockValue).prod) = 25194668663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_29
      · exact prime_oneHundredSixtySevenFI_457
      · exact prime_oneHundredSixtySevenFI_950527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 25194668663) ^ 12597334331 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 25194668663) ^ 868781678 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 25194668663) ^ 55130566 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 25194668663) ^ 26506 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_26568563647 : Nat.Prime 26568563647 := by
  apply lucas_primality 26568563647 (5 : ZMod 26568563647)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (5791, 1), (7883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (5791, 1), (7883, 1)] : List FactorBlock).map factorBlockValue).prod) = 26568563647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_97
      · exact prime_oneHundredSixtySevenFI_5791
      · exact prime_oneHundredSixtySevenFI_7883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 26568563647) ^ 13284281823 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 26568563647) ^ 8856187882 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 26568563647) ^ 273902718 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 26568563647) ^ 4587906 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 26568563647) ^ 3370362 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_27884004871 : Nat.Prime 27884004871 := by
  apply lucas_primality 27884004871 (3 : ZMod 27884004871)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (12113, 1), (76733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (12113, 1), (76733, 1)] : List FactorBlock).map factorBlockValue).prod) = 27884004871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_12113
      · exact prime_oneHundredSixtySevenFI_76733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 27884004871) ^ 13942002435 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 27884004871) ^ 9294668290 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 27884004871) ^ 5576800974 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 27884004871) ^ 2301990 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 27884004871) ^ 363390 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_27935272333 : Nat.Prime 27935272333 := by
  apply lucas_primality 27935272333 (13 : ZMod 27935272333)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (11, 1), (967, 1), (24317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (11, 1), (967, 1), (24317, 1)] : List FactorBlock).map factorBlockValue).prod) = 27935272333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_967
      · exact prime_oneHundredSixtySevenFI_24317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 27935272333) ^ 13967636166 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 27935272333) ^ 9311757444 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 27935272333) ^ 2539570212 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 27935272333) ^ 28888596 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 27935272333) ^ 1148796 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_29547899603 : Nat.Prime 29547899603 := by
  apply lucas_primality 29547899603 (2 : ZMod 29547899603)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (479, 1), (2372563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (479, 1), (2372563, 1)] : List FactorBlock).map factorBlockValue).prod) = 29547899603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_479
      · exact prime_oneHundredSixtySevenFI_2372563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 29547899603) ^ 14773949801 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 29547899603) ^ 2272915354 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 29547899603) ^ 61686638 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 29547899603) ^ 12454 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_29981528839 : Nat.Prime 29981528839 := by
  apply lucas_primality 29981528839 (6 : ZMod 29981528839)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 1), (29, 1), (1007647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 1), (29, 1), (1007647, 1)] : List FactorBlock).map factorBlockValue).prod) = 29981528839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_29
      · exact prime_oneHundredSixtySevenFI_1007647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 29981528839) ^ 14990764419 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 29981528839) ^ 9993842946 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 29981528839) ^ 1577975202 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 29981528839) ^ 1033845822 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 29981528839) ^ 29754 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_33075045457 : Nat.Prime 33075045457 := by
  apply lucas_primality 33075045457 (7 : ZMod 33075045457)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (109, 1), (6321683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (109, 1), (6321683, 1)] : List FactorBlock).map factorBlockValue).prod) = 33075045457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_109
      · exact prime_oneHundredSixtySevenFI_6321683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 33075045457) ^ 16537522728 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 33075045457) ^ 11025015152 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 33075045457) ^ 303440784 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 33075045457) ^ 5232 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_34797598919 : Nat.Prime 34797598919 := by
  apply lucas_primality 34797598919 (13 : ZMod 34797598919)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (27241, 1), (638699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (27241, 1), (638699, 1)] : List FactorBlock).map factorBlockValue).prod) = 34797598919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_27241
      · exact prime_oneHundredSixtySevenFI_638699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 34797598919) ^ 17398799459 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 34797598919) ^ 1277398 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 34797598919) ^ 54482 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_37713613027 : Nat.Prime 37713613027 := by
  apply lucas_primality 37713613027 (2 : ZMod 37713613027)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (281, 1), (22368691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (281, 1), (22368691, 1)] : List FactorBlock).map factorBlockValue).prod) = 37713613027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_281
      · exact prime_oneHundredSixtySevenFI_22368691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37713613027) ^ 18856806513 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 37713613027) ^ 12571204342 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 37713613027) ^ 134212146 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 37713613027) ^ 1686 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_40929607307 : Nat.Prime 40929607307 := by
  apply lucas_primality 40929607307 (2 : ZMod 40929607307)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (269, 1), (733, 1), (14827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (269, 1), (733, 1), (14827, 1)] : List FactorBlock).map factorBlockValue).prod) = 40929607307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_269
      · exact prime_oneHundredSixtySevenFI_733
      · exact prime_oneHundredSixtySevenFI_14827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40929607307) ^ 20464803653 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 40929607307) ^ 5847086758 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 40929607307) ^ 152154674 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 40929607307) ^ 55838482 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 40929607307) ^ 2760478 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_44890242587 : Nat.Prime 44890242587 := by
  apply lucas_primality 44890242587 (2 : ZMod 44890242587)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (45887, 1), (69877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (45887, 1), (69877, 1)] : List FactorBlock).map factorBlockValue).prod) = 44890242587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_45887
      · exact prime_oneHundredSixtySevenFI_69877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44890242587) ^ 22445121293 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 44890242587) ^ 6412891798 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 44890242587) ^ 978278 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 44890242587) ^ 642418 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_45147389831 : Nat.Prime 45147389831 := by
  apply lucas_primality 45147389831 (17 : ZMod 45147389831)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (7283, 1), (8731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (7283, 1), (8731, 1)] : List FactorBlock).map factorBlockValue).prod) = 45147389831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_71
      · exact prime_oneHundredSixtySevenFI_7283
      · exact prime_oneHundredSixtySevenFI_8731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 45147389831) ^ 22573694915 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (17 : ZMod 45147389831) ^ 9029477966 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (17 : ZMod 45147389831) ^ 635878730 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (17 : ZMod 45147389831) ^ 6199010 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (17 : ZMod 45147389831) ^ 5170930 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_47949466871 : Nat.Prime 47949466871 := by
  apply lucas_primality 47949466871 (13 : ZMod 47949466871)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (613, 1), (2473, 1), (3163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (613, 1), (2473, 1), (3163, 1)] : List FactorBlock).map factorBlockValue).prod) = 47949466871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_613
      · exact prime_oneHundredSixtySevenFI_2473
      · exact prime_oneHundredSixtySevenFI_3163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 47949466871) ^ 23974733435 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 47949466871) ^ 9589893374 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 47949466871) ^ 78220990 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 47949466871) ^ 19389190 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 47949466871) ^ 15159490 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_49595371451 : Nat.Prime 49595371451 := by
  apply lucas_primality 49595371451 (2 : ZMod 49595371451)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (73, 1), (577, 1), (23549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (73, 1), (577, 1), (23549, 1)] : List FactorBlock).map factorBlockValue).prod) = 49595371451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_73
      · exact prime_oneHundredSixtySevenFI_577
      · exact prime_oneHundredSixtySevenFI_23549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49595371451) ^ 24797685725 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 49595371451) ^ 9919074290 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 49595371451) ^ 679388650 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 49595371451) ^ 85953850 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 49595371451) ^ 2106050 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_58962959929 : Nat.Prime 58962959929 := by
  apply lucas_primality 58962959929 (7 : ZMod 58962959929)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (818929999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (818929999, 1)] : List FactorBlock).map factorBlockValue).prod) = 58962959929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_818929999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 58962959929) ^ 29481479964 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 58962959929) ^ 19654319976 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 58962959929) ^ 72 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_60046038431 : Nat.Prime 60046038431 := by
  apply lucas_primality 60046038431 (7 : ZMod 60046038431)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (8521, 1), (100669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (8521, 1), (100669, 1)] : List FactorBlock).map factorBlockValue).prod) = 60046038431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_8521
      · exact prime_oneHundredSixtySevenFI_100669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 60046038431) ^ 30023019215 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 60046038431) ^ 12009207686 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 60046038431) ^ 8578005490 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 60046038431) ^ 7046830 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 60046038431) ^ 596470 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_70269214921 : Nat.Prime 70269214921 := by
  apply lucas_primality 70269214921 (19 : ZMod 70269214921)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (585576791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (585576791, 1)] : List FactorBlock).map factorBlockValue).prod) = 70269214921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_585576791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 70269214921) ^ 35134607460 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (19 : ZMod 70269214921) ^ 23423071640 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (19 : ZMod 70269214921) ^ 14053842984 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (19 : ZMod 70269214921) ^ 120 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_85431657083 : Nat.Prime 85431657083 := by
  apply lucas_primality 85431657083 (2 : ZMod 85431657083)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (311, 1), (988129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (311, 1), (988129, 1)] : List FactorBlock).map factorBlockValue).prod) = 85431657083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_139
      · exact prime_oneHundredSixtySevenFI_311
      · exact prime_oneHundredSixtySevenFI_988129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 85431657083) ^ 42715828541 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 85431657083) ^ 614616238 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 85431657083) ^ 274699862 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 85431657083) ^ 86458 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_89436733349 : Nat.Prime 89436733349 := by
  apply lucas_primality 89436733349 (2 : ZMod 89436733349)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (1176799123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (1176799123, 1)] : List FactorBlock).map factorBlockValue).prod) = 89436733349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_1176799123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 89436733349) ^ 44718366674 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 89436733349) ^ 4707196492 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 89436733349) ^ 76 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_92232293347 : Nat.Prime 92232293347 := by
  apply lucas_primality 92232293347 (2 : ZMod 92232293347)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (14537, 1), (352481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (14537, 1), (352481, 1)] : List FactorBlock).map factorBlockValue).prod) = 92232293347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_14537
      · exact prime_oneHundredSixtySevenFI_352481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 92232293347) ^ 46116146673 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 92232293347) ^ 30744097782 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 92232293347) ^ 6344658 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 92232293347) ^ 261666 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_107272443073 : Nat.Prime 107272443073 := by
  apply lucas_primality 107272443073 (7 : ZMod 107272443073)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (23, 1), (3229, 1), (7523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (23, 1), (3229, 1), (7523, 1)] : List FactorBlock).map factorBlockValue).prod) = 107272443073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_23
      · exact prime_oneHundredSixtySevenFI_3229
      · exact prime_oneHundredSixtySevenFI_7523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 107272443073) ^ 53636221536 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 107272443073) ^ 35757481024 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 107272443073) ^ 4664019264 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 107272443073) ^ 33221568 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 107272443073) ^ 14259264 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_110198386171 : Nat.Prime 110198386171 := by
  apply lucas_primality 110198386171 (2 : ZMod 110198386171)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (17, 1), (24008363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (17, 1), (24008363, 1)] : List FactorBlock).map factorBlockValue).prod) = 110198386171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_17
      · exact prime_oneHundredSixtySevenFI_24008363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 110198386171) ^ 55099193085 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 110198386171) ^ 36732795390 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 110198386171) ^ 22039677234 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 110198386171) ^ 6482258010 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 110198386171) ^ 4590 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_122280343109 : Nat.Prime 122280343109 := by
  apply lucas_primality 122280343109 (2 : ZMod 122280343109)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 2), (19, 1), (1899589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 2), (19, 1), (1899589, 1)] : List FactorBlock).map factorBlockValue).prod) = 122280343109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_1899589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 122280343109) ^ 61140171554 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 122280343109) ^ 17468620444 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 122280343109) ^ 11116394828 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 122280343109) ^ 6435807532 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 122280343109) ^ 64372 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_125539935277 : Nat.Prime 125539935277 := by
  apply lucas_primality 125539935277 (2 : ZMod 125539935277)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (163, 1), (9168853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (163, 1), (9168853, 1)] : List FactorBlock).map factorBlockValue).prod) = 125539935277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_163
      · exact prime_oneHundredSixtySevenFI_9168853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 125539935277) ^ 62769967638 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 125539935277) ^ 41846645092 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 125539935277) ^ 17934276468 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 125539935277) ^ 770183652 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 125539935277) ^ 13692 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_150292621489 : Nat.Prime 150292621489 := by
  apply lucas_primality 150292621489 (7 : ZMod 150292621489)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (149, 1), (21014069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (149, 1), (21014069, 1)] : List FactorBlock).map factorBlockValue).prod) = 150292621489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_149
      · exact prime_oneHundredSixtySevenFI_21014069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 150292621489) ^ 75146310744 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 150292621489) ^ 50097540496 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 150292621489) ^ 1008675312 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 150292621489) ^ 7152 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_188600021821 : Nat.Prime 188600021821 := by
  apply lucas_primality 188600021821 (2 : ZMod 188600021821)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (149682557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (149682557, 1)] : List FactorBlock).map factorBlockValue).prod) = 188600021821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_149682557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 188600021821) ^ 94300010910 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 188600021821) ^ 62866673940 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 188600021821) ^ 37720004364 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 188600021821) ^ 26942860260 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 188600021821) ^ 1260 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_189045555533 : Nat.Prime 189045555533 := by
  apply lucas_primality 189045555533 (2 : ZMod 189045555533)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (239, 1), (11632141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (239, 1), (11632141, 1)] : List FactorBlock).map factorBlockValue).prod) = 189045555533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_17
      · exact prime_oneHundredSixtySevenFI_239
      · exact prime_oneHundredSixtySevenFI_11632141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 189045555533) ^ 94522777766 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 189045555533) ^ 11120326796 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 189045555533) ^ 790985588 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 189045555533) ^ 16252 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_226445213359 : Nat.Prime 226445213359 := by
  apply lucas_primality 226445213359 (6 : ZMod 226445213359)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (7, 1), (13, 1), (5120183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (7, 1), (13, 1), (5120183, 1)] : List FactorBlock).map factorBlockValue).prod) = 226445213359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_5120183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 226445213359) ^ 113222606679 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 226445213359) ^ 75481737786 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 226445213359) ^ 32349316194 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 226445213359) ^ 17418862566 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 226445213359) ^ 44226 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_228985732007 : Nat.Prime 228985732007 := by
  apply lucas_primality 228985732007 (5 : ZMod 228985732007)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (233, 1), (1499, 1), (327809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (233, 1), (1499, 1), (327809, 1)] : List FactorBlock).map factorBlockValue).prod) = 228985732007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_233
      · exact prime_oneHundredSixtySevenFI_1499
      · exact prime_oneHundredSixtySevenFI_327809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 228985732007) ^ 114492866003 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 228985732007) ^ 982771382 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 228985732007) ^ 152758994 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 228985732007) ^ 698534 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_232960599869 : Nat.Prime 232960599869 := by
  apply lucas_primality 232960599869 (2 : ZMod 232960599869)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (18911, 1), (3079697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (18911, 1), (3079697, 1)] : List FactorBlock).map factorBlockValue).prod) = 232960599869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_18911
      · exact prime_oneHundredSixtySevenFI_3079697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 232960599869) ^ 116480299934 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 232960599869) ^ 12318788 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 232960599869) ^ 75644 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_249366878489 : Nat.Prime 249366878489 := by
  apply lucas_primality 249366878489 (3 : ZMod 249366878489)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13, 1), (19, 1), (2251, 1), (8009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13, 1), (19, 1), (2251, 1), (8009, 1)] : List FactorBlock).map factorBlockValue).prod) = 249366878489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_2251
      · exact prime_oneHundredSixtySevenFI_8009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 249366878489) ^ 124683439244 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 249366878489) ^ 35623839784 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 249366878489) ^ 19182067576 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 249366878489) ^ 13124572552 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 249366878489) ^ 110780488 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 249366878489) ^ 31135832 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_264483781853 : Nat.Prime 264483781853 := by
  apply lucas_primality 264483781853 (2 : ZMod 264483781853)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1499, 1), (44110037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1499, 1), (44110037, 1)] : List FactorBlock).map factorBlockValue).prod) = 264483781853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_1499
      · exact prime_oneHundredSixtySevenFI_44110037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 264483781853) ^ 132241890926 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 264483781853) ^ 176440148 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 264483781853) ^ 5996 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_314099627273 : Nat.Prime 314099627273 := by
  apply lucas_primality 314099627273 (3 : ZMod 314099627273)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (443, 1), (88628563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (443, 1), (88628563, 1)] : List FactorBlock).map factorBlockValue).prod) = 314099627273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_443
      · exact prime_oneHundredSixtySevenFI_88628563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 314099627273) ^ 157049813636 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 314099627273) ^ 709028504 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 314099627273) ^ 3544 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_315548325769 : Nat.Prime 315548325769 := by
  apply lucas_primality 315548325769 (7 : ZMod 315548325769)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (67, 1), (15095117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (67, 1), (15095117, 1)] : List FactorBlock).map factorBlockValue).prod) = 315548325769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_67
      · exact prime_oneHundredSixtySevenFI_15095117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 315548325769) ^ 157774162884 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 315548325769) ^ 105182775256 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 315548325769) ^ 24272948136 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 315548325769) ^ 4709676504 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 315548325769) ^ 20904 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_370112051189 : Nat.Prime 370112051189 := by
  apply lucas_primality 370112051189 (2 : ZMod 370112051189)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (63113, 1), (133279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (63113, 1), (133279, 1)] : List FactorBlock).map factorBlockValue).prod) = 370112051189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_63113
      · exact prime_oneHundredSixtySevenFI_133279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 370112051189) ^ 185056025594 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 370112051189) ^ 33646550108 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 370112051189) ^ 5864276 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 370112051189) ^ 2776972 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_380995484899 : Nat.Prime 380995484899 := by
  apply lucas_primality 380995484899 (2 : ZMod 380995484899)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (1307, 1), (365293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (1307, 1), (365293, 1)] : List FactorBlock).map factorBlockValue).prod) = 380995484899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_1307
      · exact prime_oneHundredSixtySevenFI_365293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 380995484899) ^ 190497742449 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 380995484899) ^ 126998494966 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 380995484899) ^ 54427926414 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 380995484899) ^ 20052393942 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 380995484899) ^ 291503814 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 380995484899) ^ 1042986 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_629040571123 : Nat.Prime 629040571123 := by
  apply lucas_primality 629040571123 (2 : ZMod 629040571123)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (316507, 1), (331241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (316507, 1), (331241, 1)] : List FactorBlock).map factorBlockValue).prod) = 629040571123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_316507
      · exact prime_oneHundredSixtySevenFI_331241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 629040571123) ^ 314520285561 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 629040571123) ^ 209680190374 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 629040571123) ^ 1987446 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 629040571123) ^ 1899042 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_731102265797 : Nat.Prime 731102265797 := by
  apply lucas_primality 731102265797 (2 : ZMod 731102265797)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (3730113601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (3730113601, 1)] : List FactorBlock).map factorBlockValue).prod) = 731102265797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_3730113601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 731102265797) ^ 365551132898 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 731102265797) ^ 104443180828 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 731102265797) ^ 196 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_835142374057 : Nat.Prime 835142374057 := by
  apply lucas_primality 835142374057 (5 : ZMod 835142374057)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (34797598919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (34797598919, 1)] : List FactorBlock).map factorBlockValue).prod) = 835142374057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_34797598919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 835142374057) ^ 417571187028 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 835142374057) ^ 278380791352 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 835142374057) ^ 24 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1212111394027 : Nat.Prime 1212111394027 := by
  apply lucas_primality 1212111394027 (3 : ZMod 1212111394027)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (15539889667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (15539889667, 1)] : List FactorBlock).map factorBlockValue).prod) = 1212111394027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_15539889667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1212111394027) ^ 606055697013 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1212111394027) ^ 404037131342 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1212111394027) ^ 93239338002 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1212111394027) ^ 78 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1530558781033 : Nat.Prime 1530558781033 := by
  apply lucas_primality 1530558781033 (5 : ZMod 1530558781033)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (173, 1), (368631691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (173, 1), (368631691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1530558781033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_173
      · exact prime_oneHundredSixtySevenFI_368631691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1530558781033) ^ 765279390516 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1530558781033) ^ 510186260344 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1530558781033) ^ 8847160584 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1530558781033) ^ 4152 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1545568713257 : Nat.Prime 1545568713257 := by
  apply lucas_primality 1545568713257 (3 : ZMod 1545568713257)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (71443, 1), (2704199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (71443, 1), (2704199, 1)] : List FactorBlock).map factorBlockValue).prod) = 1545568713257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_71443
      · exact prime_oneHundredSixtySevenFI_2704199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1545568713257) ^ 772784356628 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1545568713257) ^ 21633592 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1545568713257) ^ 571544 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1580030177903 : Nat.Prime 1580030177903 := by
  apply lucas_primality 1580030177903 (5 : ZMod 1580030177903)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (29, 1), (211, 1), (1451, 1), (8089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (29, 1), (211, 1), (1451, 1), (8089, 1)] : List FactorBlock).map factorBlockValue).prod) = 1580030177903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_29
      · exact prime_oneHundredSixtySevenFI_211
      · exact prime_oneHundredSixtySevenFI_1451
      · exact prime_oneHundredSixtySevenFI_8089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1580030177903) ^ 790015088951 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1580030177903) ^ 143639107082 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1580030177903) ^ 54483799238 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1580030177903) ^ 7488294682 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1580030177903) ^ 1088925002 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1580030177903) ^ 195330718 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1808574742463 : Nat.Prime 1808574742463 := by
  apply lucas_primality 1808574742463 (5 : ZMod 1808574742463)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (457, 1), (1978746983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (457, 1), (1978746983, 1)] : List FactorBlock).map factorBlockValue).prod) = 1808574742463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_457
      · exact prime_oneHundredSixtySevenFI_1978746983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1808574742463) ^ 904287371231 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1808574742463) ^ 3957493966 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1808574742463) ^ 914 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_2064870701017 : Nat.Prime 2064870701017 := by
  apply lucas_primality 2064870701017 (5 : ZMod 2064870701017)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (173, 1), (497319533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (173, 1), (497319533, 1)] : List FactorBlock).map factorBlockValue).prod) = 2064870701017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_173
      · exact prime_oneHundredSixtySevenFI_497319533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2064870701017) ^ 1032435350508 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2064870701017) ^ 688290233672 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2064870701017) ^ 11935668792 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2064870701017) ^ 4152 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_2196564665453 : Nat.Prime 2196564665453 := by
  apply lucas_primality 2196564665453 (2 : ZMod 2196564665453)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (73, 1), (242660701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (73, 1), (242660701, 1)] : List FactorBlock).map factorBlockValue).prod) = 2196564665453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_31
      · exact prime_oneHundredSixtySevenFI_73
      · exact prime_oneHundredSixtySevenFI_242660701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2196564665453) ^ 1098282332726 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2196564665453) ^ 70856924692 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2196564665453) ^ 30089926924 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2196564665453) ^ 9052 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_2646637777463 : Nat.Prime 2646637777463 := by
  apply lucas_primality 2646637777463 (5 : ZMod 2646637777463)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (189045555533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (189045555533, 1)] : List FactorBlock).map factorBlockValue).prod) = 2646637777463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_189045555533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2646637777463) ^ 1323318888731 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2646637777463) ^ 378091111066 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2646637777463) ^ 14 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_2810414903111 : Nat.Prime 2810414903111 := by
  apply lucas_primality 2810414903111 (7 : ZMod 2810414903111)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2851, 1), (98576461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2851, 1), (98576461, 1)] : List FactorBlock).map factorBlockValue).prod) = 2810414903111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_2851
      · exact prime_oneHundredSixtySevenFI_98576461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2810414903111) ^ 1405207451555 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2810414903111) ^ 562082980622 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2810414903111) ^ 985764610 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2810414903111) ^ 28510 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_2823143494733 : Nat.Prime 2823143494733 := by
  apply lucas_primality 2823143494733 (2 : ZMod 2823143494733)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (17, 1), (2213, 1), (1705493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (17, 1), (2213, 1), (1705493, 1)] : List FactorBlock).map factorBlockValue).prod) = 2823143494733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_17
      · exact prime_oneHundredSixtySevenFI_2213
      · exact prime_oneHundredSixtySevenFI_1705493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2823143494733) ^ 1411571747366 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2823143494733) ^ 256649408612 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2823143494733) ^ 166067264396 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2823143494733) ^ 1275708764 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2823143494733) ^ 1655324 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_2979727728847 : Nat.Prime 2979727728847 := by
  apply lucas_primality 2979727728847 (5 : ZMod 2979727728847)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (45147389831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (45147389831, 1)] : List FactorBlock).map factorBlockValue).prod) = 2979727728847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_45147389831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2979727728847) ^ 1489863864423 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2979727728847) ^ 993242576282 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2979727728847) ^ 270884338986 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2979727728847) ^ 66 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_3085589801647 : Nat.Prime 3085589801647 := by
  apply lucas_primality 3085589801647 (6 : ZMod 3085589801647)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (12641, 1), (1232797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (12641, 1), (1232797, 1)] : List FactorBlock).map factorBlockValue).prod) = 3085589801647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_12641
      · exact prime_oneHundredSixtySevenFI_1232797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3085589801647) ^ 1542794900823 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 3085589801647) ^ 1028529933882 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 3085589801647) ^ 280508163786 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 3085589801647) ^ 244093806 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 3085589801647) ^ 2502918 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_3109478435809 : Nat.Prime 3109478435809 := by
  apply lucas_primality 3109478435809 (13 : ZMod 3109478435809)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (919, 1), (2073251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (919, 1), (2073251, 1)] : List FactorBlock).map factorBlockValue).prod) = 3109478435809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_17
      · exact prime_oneHundredSixtySevenFI_919
      · exact prime_oneHundredSixtySevenFI_2073251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3109478435809) ^ 1554739217904 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 3109478435809) ^ 1036492811936 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 3109478435809) ^ 182910496224 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 3109478435809) ^ 3383545632 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 3109478435809) ^ 1499808 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_3160060355807 : Nat.Prime 3160060355807 := by
  apply lucas_primality 3160060355807 (5 : ZMod 3160060355807)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1580030177903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1580030177903, 1)] : List FactorBlock).map factorBlockValue).prod) = 3160060355807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_1580030177903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 3160060355807) ^ 1580030177903 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3160060355807) ^ 2 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_3600507948211 : Nat.Prime 3600507948211 := by
  apply lucas_primality 3600507948211 (2 : ZMod 3600507948211)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (29, 1), (499, 1), (307171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (29, 1), (499, 1), (307171, 1)] : List FactorBlock).map factorBlockValue).prod) = 3600507948211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_29
      · exact prime_oneHundredSixtySevenFI_499
      · exact prime_oneHundredSixtySevenFI_307171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3600507948211) ^ 1800253974105 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3600507948211) ^ 1200169316070 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3600507948211) ^ 720101589642 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3600507948211) ^ 124155446490 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3600507948211) ^ 7215446790 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3600507948211) ^ 11721510 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_4236010245151 : Nat.Prime 4236010245151 := by
  apply lucas_primality 4236010245151 (3 : ZMod 4236010245151)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (79, 1), (139, 1), (2571721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (79, 1), (139, 1), (2571721, 1)] : List FactorBlock).map factorBlockValue).prod) = 4236010245151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_79
      · exact prime_oneHundredSixtySevenFI_139
      · exact prime_oneHundredSixtySevenFI_2571721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4236010245151) ^ 2118005122575 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4236010245151) ^ 1412003415050 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4236010245151) ^ 847202049030 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4236010245151) ^ 53620382850 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4236010245151) ^ 30474893850 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4236010245151) ^ 1647150 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_4504692580733 : Nat.Prime 4504692580733 := by
  apply lucas_primality 4504692580733 (2 : ZMod 4504692580733)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (70999, 1), (15861817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (70999, 1), (15861817, 1)] : List FactorBlock).map factorBlockValue).prod) = 4504692580733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_70999
      · exact prime_oneHundredSixtySevenFI_15861817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4504692580733) ^ 2252346290366 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4504692580733) ^ 63447268 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4504692580733) ^ 283996 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_5358633174619 : Nat.Prime 5358633174619 := by
  apply lucas_primality 5358633174619 (2 : ZMod 5358633174619)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (151, 1), (1187, 1), (293107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (151, 1), (1187, 1), (293107, 1)] : List FactorBlock).map factorBlockValue).prod) = 5358633174619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_17
      · exact prime_oneHundredSixtySevenFI_151
      · exact prime_oneHundredSixtySevenFI_1187
      · exact prime_oneHundredSixtySevenFI_293107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5358633174619) ^ 2679316587309 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5358633174619) ^ 1786211058206 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5358633174619) ^ 315213716154 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5358633174619) ^ 35487636918 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5358633174619) ^ 4514434014 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5358633174619) ^ 18282174 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_5620829806223 : Nat.Prime 5620829806223 := by
  apply lucas_primality 5620829806223 (5 : ZMod 5620829806223)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2810414903111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2810414903111, 1)] : List FactorBlock).map factorBlockValue).prod) = 5620829806223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_2810414903111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 5620829806223) ^ 2810414903111 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5620829806223) ^ 2 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_6070288014737 : Nat.Prime 6070288014737 := by
  apply lucas_primality 6070288014737 (3 : ZMod 6070288014737)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (1867, 1), (18473633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (1867, 1), (18473633, 1)] : List FactorBlock).map factorBlockValue).prod) = 6070288014737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_1867
      · exact prime_oneHundredSixtySevenFI_18473633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6070288014737) ^ 3035144007368 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6070288014737) ^ 551844364976 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6070288014737) ^ 3251359408 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6070288014737) ^ 328592 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_6290405711231 : Nat.Prime 6290405711231 := by
  apply lucas_primality 6290405711231 (11 : ZMod 6290405711231)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (629040571123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (629040571123, 1)] : List FactorBlock).map factorBlockValue).prod) = 6290405711231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_629040571123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 6290405711231) ^ 3145202855615 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 6290405711231) ^ 1258081142246 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 6290405711231) ^ 10 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_7723615901257 : Nat.Prime 7723615901257 := by
  apply lucas_primality 7723615901257 (5 : ZMod 7723615901257)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (107272443073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (107272443073, 1)] : List FactorBlock).map factorBlockValue).prod) = 7723615901257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_107272443073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7723615901257) ^ 3861807950628 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7723615901257) ^ 2574538633752 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7723615901257) ^ 72 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_12596276615077 : Nat.Prime 12596276615077 := by
  apply lucas_primality 12596276615077 (2 : ZMod 12596276615077)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (11, 1), (677, 1), (6712129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (11, 1), (677, 1), (6712129, 1)] : List FactorBlock).map factorBlockValue).prod) = 12596276615077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_677
      · exact prime_oneHundredSixtySevenFI_6712129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12596276615077) ^ 6298138307538 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 12596276615077) ^ 4198758871692 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 12596276615077) ^ 1799468087868 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 12596276615077) ^ 1145116055916 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 12596276615077) ^ 18606021588 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 12596276615077) ^ 1876644 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_15777128132609 : Nat.Prime 15777128132609 := by
  apply lucas_primality 15777128132609 (3 : ZMod 15777128132609)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 12), (227, 1), (521, 1), (32569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 12), (227, 1), (521, 1), (32569, 1)] : List FactorBlock).map factorBlockValue).prod) = 15777128132609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_227
      · exact prime_oneHundredSixtySevenFI_521
      · exact prime_oneHundredSixtySevenFI_32569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 15777128132609) ^ 7888564066304 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15777128132609) ^ 69502767104 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15777128132609) ^ 30282395648 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15777128132609) ^ 484421632 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_26948359863043 : Nat.Prime 26948359863043 := by
  apply lucas_primality 26948359863043 (3 : ZMod 26948359863043)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37123, 1), (120986809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37123, 1), (120986809, 1)] : List FactorBlock).map factorBlockValue).prod) = 26948359863043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_37123
      · exact prime_oneHundredSixtySevenFI_120986809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26948359863043) ^ 13474179931521 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 26948359863043) ^ 8982786621014 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 26948359863043) ^ 725920854 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 26948359863043) ^ 222738 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_31951343081293 : Nat.Prime 31951343081293 := by
  apply lucas_primality 31951343081293 (2 : ZMod 31951343081293)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (269, 1), (9898185589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (269, 1), (9898185589, 1)] : List FactorBlock).map factorBlockValue).prod) = 31951343081293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_269
      · exact prime_oneHundredSixtySevenFI_9898185589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31951343081293) ^ 15975671540646 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 31951343081293) ^ 10650447693764 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 31951343081293) ^ 118778227068 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 31951343081293) ^ 3228 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_37991261488513 : Nat.Prime 37991261488513 := by
  apply lucas_primality 37991261488513 (5 : ZMod 37991261488513)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (541, 1), (182875373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (541, 1), (182875373, 1)] : List FactorBlock).map factorBlockValue).prod) = 37991261488513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_541
      · exact prime_oneHundredSixtySevenFI_182875373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 37991261488513) ^ 18995630744256 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 37991261488513) ^ 12663753829504 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 37991261488513) ^ 70224143232 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 37991261488513) ^ 207744 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_49004355142163 : Nat.Prime 49004355142163 := by
  apply lucas_primality 49004355142163 (2 : ZMod 49004355142163)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (73, 1), (47949466871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (73, 1), (47949466871, 1)] : List FactorBlock).map factorBlockValue).prod) = 49004355142163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_73
      · exact prime_oneHundredSixtySevenFI_47949466871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 49004355142163) ^ 24502177571081 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 49004355142163) ^ 7000622163166 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 49004355142163) ^ 671292536194 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 49004355142163) ^ 1022 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_49303747199921 : Nat.Prime 49303747199921 := by
  apply lucas_primality 49303747199921 (3 : ZMod 49303747199921)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (619, 1), (995633021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (619, 1), (995633021, 1)] : List FactorBlock).map factorBlockValue).prod) = 49303747199921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_619
      · exact prime_oneHundredSixtySevenFI_995633021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 49303747199921) ^ 24651873599960 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 49303747199921) ^ 9860749439984 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 49303747199921) ^ 79650641680 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 49303747199921) ^ 49520 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_65800700600953 : Nat.Prime 65800700600953 := by
  apply lucas_primality 65800700600953 (7 : ZMod 65800700600953)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (283, 1), (1231, 1), (253871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (283, 1), (1231, 1), (253871, 1)] : List FactorBlock).map factorBlockValue).prod) = 65800700600953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_31
      · exact prime_oneHundredSixtySevenFI_283
      · exact prime_oneHundredSixtySevenFI_1231
      · exact prime_oneHundredSixtySevenFI_253871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 65800700600953) ^ 32900350300476 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 65800700600953) ^ 21933566866984 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 65800700600953) ^ 2122603245192 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 65800700600953) ^ 232511309544 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 65800700600953) ^ 53453046792 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 65800700600953) ^ 259189512 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_79076327956309 : Nat.Prime 79076327956309 := by
  apply lucas_primality 79076327956309 (2 : ZMod 79076327956309)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2196564665453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2196564665453, 1)] : List FactorBlock).map factorBlockValue).prod) = 79076327956309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_2196564665453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 79076327956309) ^ 39538163978154 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 79076327956309) ^ 26358775985436 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 79076327956309) ^ 36 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_83891250011083 : Nat.Prime 83891250011083 := by
  apply lucas_primality 83891250011083 (2 : ZMod 83891250011083)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (181, 1), (1663, 1), (876433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (181, 1), (1663, 1), (876433, 1)] : List FactorBlock).map factorBlockValue).prod) = 83891250011083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_53
      · exact prime_oneHundredSixtySevenFI_181
      · exact prime_oneHundredSixtySevenFI_1663
      · exact prime_oneHundredSixtySevenFI_876433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 83891250011083) ^ 41945625005541 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 83891250011083) ^ 27963750003694 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 83891250011083) ^ 1582853773794 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 83891250011083) ^ 463487569122 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 83891250011083) ^ 50445730614 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 83891250011083) ^ 95718954 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_88659702814849 : Nat.Prime 88659702814849 := by
  apply lucas_primality 88659702814849 (17 : ZMod 88659702814849)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (11, 1), (20989512977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (11, 1), (20989512977, 1)] : List FactorBlock).map factorBlockValue).prod) = 88659702814849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_20989512977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 88659702814849) ^ 44329851407424 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (17 : ZMod 88659702814849) ^ 29553234271616 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (17 : ZMod 88659702814849) ^ 8059972983168 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (17 : ZMod 88659702814849) ^ 4224 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_91141993011103 : Nat.Prime 91141993011103 := by
  apply lucas_primality 91141993011103 (3 : ZMod 91141993011103)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (125539935277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (125539935277, 1)] : List FactorBlock).map factorBlockValue).prod) = 91141993011103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_125539935277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 91141993011103) ^ 45570996505551 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 91141993011103) ^ 30380664337034 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 91141993011103) ^ 8285635728282 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 91141993011103) ^ 726 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_104052850052891 : Nat.Prime 104052850052891 := by
  apply lucas_primality 104052850052891 (2 : ZMod 104052850052891)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (983, 1), (10585233983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (983, 1), (10585233983, 1)] : List FactorBlock).map factorBlockValue).prod) = 104052850052891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_983
      · exact prime_oneHundredSixtySevenFI_10585233983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 104052850052891) ^ 52026425026445 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 104052850052891) ^ 20810570010578 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 104052850052891) ^ 105852339830 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 104052850052891) ^ 9830 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_105145711896089 : Nat.Prime 105145711896089 := by
  apply lucas_primality 105145711896089 (3 : ZMod 105145711896089)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2659, 1), (4942916129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2659, 1), (4942916129, 1)] : List FactorBlock).map factorBlockValue).prod) = 105145711896089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_2659
      · exact prime_oneHundredSixtySevenFI_4942916129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 105145711896089) ^ 52572855948044 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 105145711896089) ^ 39543329032 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 105145711896089) ^ 21272 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_106276981411253 : Nat.Prime 106276981411253 := by
  apply lucas_primality 106276981411253 (2 : ZMod 106276981411253)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (311, 1), (85431657083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (311, 1), (85431657083, 1)] : List FactorBlock).map factorBlockValue).prod) = 106276981411253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_311
      · exact prime_oneHundredSixtySevenFI_85431657083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 106276981411253) ^ 53138490705626 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 106276981411253) ^ 341726628332 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 106276981411253) ^ 1244 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_122478017651371 : Nat.Prime 122478017651371 := by
  apply lucas_primality 122478017651371 (3 : ZMod 122478017651371)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 1), (19139, 1), (4182611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 1), (19139, 1), (4182611, 1)] : List FactorBlock).map factorBlockValue).prod) = 122478017651371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_17
      · exact prime_oneHundredSixtySevenFI_19139
      · exact prime_oneHundredSixtySevenFI_4182611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 122478017651371) ^ 61239008825685 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 122478017651371) ^ 40826005883790 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 122478017651371) ^ 24495603530274 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 122478017651371) ^ 7204589273610 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 122478017651371) ^ 6399394830 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 122478017651371) ^ 29282670 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_139649401306699 : Nat.Prime 139649401306699 := by
  apply lucas_primality 139649401306699 (2 : ZMod 139649401306699)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9473, 1), (34679, 1), (70849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9473, 1), (34679, 1), (70849, 1)] : List FactorBlock).map factorBlockValue).prod) = 139649401306699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_9473
      · exact prime_oneHundredSixtySevenFI_34679
      · exact prime_oneHundredSixtySevenFI_70849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 139649401306699) ^ 69824700653349 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 139649401306699) ^ 46549800435566 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 139649401306699) ^ 14741834826 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 139649401306699) ^ 4026915462 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 139649401306699) ^ 1971085002 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_184226420328299 : Nat.Prime 184226420328299 := by
  apply lucas_primality 184226420328299 (2 : ZMod 184226420328299)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3467, 1), (26568563647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3467, 1), (26568563647, 1)] : List FactorBlock).map factorBlockValue).prod) = 184226420328299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3467
      · exact prime_oneHundredSixtySevenFI_26568563647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 184226420328299) ^ 92113210164149 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 184226420328299) ^ 53137127294 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 184226420328299) ^ 6934 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_200183729666747 : Nat.Prime 200183729666747 := by
  apply lucas_primality 200183729666747 (2 : ZMod 200183729666747)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (89, 1), (109, 1), (2297, 1), (33773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (89, 1), (109, 1), (2297, 1), (33773, 1)] : List FactorBlock).map factorBlockValue).prod) = 200183729666747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_89
      · exact prime_oneHundredSixtySevenFI_109
      · exact prime_oneHundredSixtySevenFI_2297
      · exact prime_oneHundredSixtySevenFI_33773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 200183729666747) ^ 100091864833373 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 200183729666747) ^ 28597675666678 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 200183729666747) ^ 10535985771934 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 200183729666747) ^ 2249255389514 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 200183729666747) ^ 1836547978594 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 200183729666747) ^ 87150078218 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 200183729666747) ^ 5927330402 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_948301481887213 : Nat.Prime 948301481887213 := by
  apply lucas_primality 948301481887213 (2 : ZMod 948301481887213)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (179, 1), (587, 1), (787, 1), (20333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (179, 1), (587, 1), (787, 1), (20333, 1)] : List FactorBlock).map factorBlockValue).prod) = 948301481887213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_47
      · exact prime_oneHundredSixtySevenFI_179
      · exact prime_oneHundredSixtySevenFI_587
      · exact prime_oneHundredSixtySevenFI_787
      · exact prime_oneHundredSixtySevenFI_20333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 948301481887213) ^ 474150740943606 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 948301481887213) ^ 316100493962404 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 948301481887213) ^ 20176627274196 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 948301481887213) ^ 5297773641828 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 948301481887213) ^ 1615505079876 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 948301481887213) ^ 1204957410276 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 948301481887213) ^ 46638542364 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1604040431798201 : Nat.Prime 1604040431798201 := by
  apply lucas_primality 1604040431798201 (3 : ZMod 1604040431798201)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (11, 2), (102019, 1), (649709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (11, 2), (102019, 1), (649709, 1)] : List FactorBlock).map factorBlockValue).prod) = 1604040431798201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_102019
      · exact prime_oneHundredSixtySevenFI_649709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1604040431798201) ^ 802020215899100 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1604040431798201) ^ 320808086359640 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1604040431798201) ^ 145821857436200 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1604040431798201) ^ 15722957800 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1604040431798201) ^ 2468859800 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1819666968074531 : Nat.Prime 1819666968074531 := by
  apply lucas_primality 1819666968074531 (2 : ZMod 1819666968074531)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (18521, 1), (9824885093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (18521, 1), (9824885093, 1)] : List FactorBlock).map factorBlockValue).prod) = 1819666968074531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_18521
      · exact prime_oneHundredSixtySevenFI_9824885093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1819666968074531) ^ 909833484037265 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1819666968074531) ^ 363933393614906 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1819666968074531) ^ 98248850930 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1819666968074531) ^ 185210 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_2749455050663513 : Nat.Prime 2749455050663513 := by
  apply lucas_primality 2749455050663513 (3 : ZMod 2749455050663513)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (109, 1), (5209, 1), (605307119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (109, 1), (5209, 1), (605307119, 1)] : List FactorBlock).map factorBlockValue).prod) = 2749455050663513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_109
      · exact prime_oneHundredSixtySevenFI_5209
      · exact prime_oneHundredSixtySevenFI_605307119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2749455050663513) ^ 1374727525331756 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2749455050663513) ^ 25224358262968 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2749455050663513) ^ 527827807768 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2749455050663513) ^ 4542248 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_4888845378349451 : Nat.Prime 4888845378349451 := by
  apply lucas_primality 4888845378349451 (6 : ZMod 4888845378349451)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (61, 1), (228985732007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (61, 1), (228985732007, 1)] : List FactorBlock).map factorBlockValue).prod) = 4888845378349451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_61
      · exact prime_oneHundredSixtySevenFI_228985732007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4888845378349451) ^ 2444422689174725 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4888845378349451) ^ 977769075669890 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4888845378349451) ^ 698406482621350 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4888845378349451) ^ 80145006202450 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4888845378349451) ^ 21350 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_5028108410867683 : Nat.Prime 5028108410867683 := by
  apply lucas_primality 5028108410867683 (2 : ZMod 5028108410867683)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (2417, 1), (136483, 1), (362911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (2417, 1), (136483, 1), (362911, 1)] : List FactorBlock).map factorBlockValue).prod) = 5028108410867683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_2417
      · exact prime_oneHundredSixtySevenFI_136483
      · exact prime_oneHundredSixtySevenFI_362911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5028108410867683) ^ 2514054205433841 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5028108410867683) ^ 1676036136955894 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5028108410867683) ^ 718301201552526 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5028108410867683) ^ 2080309644546 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5028108410867683) ^ 36840547254 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5028108410867683) ^ 13854935262 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_7439038837657943 : Nat.Prime 7439038837657943 := by
  apply lucas_primality 7439038837657943 (5 : ZMod 7439038837657943)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (6581, 1), (5487287497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (6581, 1), (5487287497, 1)] : List FactorBlock).map factorBlockValue).prod) = 7439038837657943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_103
      · exact prime_oneHundredSixtySevenFI_6581
      · exact prime_oneHundredSixtySevenFI_5487287497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7439038837657943) ^ 3719519418828971 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7439038837657943) ^ 72223678035514 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7439038837657943) ^ 1130381224382 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7439038837657943) ^ 1355686 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_9611342825104177 : Nat.Prime 9611342825104177 := by
  apply lucas_primality 9611342825104177 (5 : ZMod 9611342825104177)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (167, 1), (92232293347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (167, 1), (92232293347, 1)] : List FactorBlock).map factorBlockValue).prod) = 9611342825104177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_167
      · exact prime_oneHundredSixtySevenFI_92232293347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9611342825104177) ^ 4805671412552088 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 9611342825104177) ^ 3203780941701392 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 9611342825104177) ^ 739334063469552 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 9611342825104177) ^ 57552951048528 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 9611342825104177) ^ 104208 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_9777690756698903 : Nat.Prime 9777690756698903 := by
  apply lucas_primality 9777690756698903 (5 : ZMod 9777690756698903)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4888845378349451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4888845378349451, 1)] : List FactorBlock).map factorBlockValue).prod) = 9777690756698903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_4888845378349451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 9777690756698903) ^ 4888845378349451 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 9777690756698903) ^ 2 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_11931506822380883 : Nat.Prime 11931506822380883 := by
  apply lucas_primality 11931506822380883 (2 : ZMod 11931506822380883)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (49303747199921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (49303747199921, 1)] : List FactorBlock).map factorBlockValue).prod) = 11931506822380883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_49303747199921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11931506822380883) ^ 5965753411190441 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11931506822380883) ^ 1084682438398262 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11931506822380883) ^ 242 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_12781485522411769 : Nat.Prime 12781485522411769 := by
  apply lucas_primality 12781485522411769 (13 : ZMod 12781485522411769)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (31, 1), (191, 1), (29981528839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (31, 1), (191, 1), (29981528839, 1)] : List FactorBlock).map factorBlockValue).prod) = 12781485522411769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_31
      · exact prime_oneHundredSixtySevenFI_191
      · exact prime_oneHundredSixtySevenFI_29981528839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 12781485522411769) ^ 6390742761205884 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 12781485522411769) ^ 4260495174137256 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 12781485522411769) ^ 412305984593928 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 12781485522411769) ^ 66918772368648 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 12781485522411769) ^ 426312 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_16385806564269101 : Nat.Prime 16385806564269101 := by
  apply lucas_primality 16385806564269101 (2 : ZMod 16385806564269101)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (397, 1), (58962959929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (397, 1), (58962959929, 1)] : List FactorBlock).map factorBlockValue).prod) = 16385806564269101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_397
      · exact prime_oneHundredSixtySevenFI_58962959929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16385806564269101) ^ 8192903282134550 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 16385806564269101) ^ 3277161312853820 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 16385806564269101) ^ 2340829509181300 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 16385806564269101) ^ 41274071950300 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 16385806564269101) ^ 277900 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_18063245379444413 : Nat.Prime 18063245379444413 := by
  apply lucas_primality 18063245379444413 (2 : ZMod 18063245379444413)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (1361029, 1), (67713043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (1361029, 1), (67713043, 1)] : List FactorBlock).map factorBlockValue).prod) = 18063245379444413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_1361029
      · exact prime_oneHundredSixtySevenFI_67713043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18063245379444413) ^ 9031622689722206 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 18063245379444413) ^ 2580463625634916 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 18063245379444413) ^ 13271756428 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 18063245379444413) ^ 266761684 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_25138275126985861 : Nat.Prime 25138275126985861 := by
  apply lucas_primality 25138275126985861 (2 : ZMod 25138275126985861)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (29, 1), (863, 1), (2391538579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (29, 1), (863, 1), (2391538579, 1)] : List FactorBlock).map factorBlockValue).prod) = 25138275126985861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_29
      · exact prime_oneHundredSixtySevenFI_863
      · exact prime_oneHundredSixtySevenFI_2391538579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25138275126985861) ^ 12569137563492930 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25138275126985861) ^ 8379425042328620 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25138275126985861) ^ 5027655025397172 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25138275126985861) ^ 3591182160997980 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25138275126985861) ^ 866837073344340 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25138275126985861) ^ 29128939892220 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25138275126985861) ^ 10511340 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_26112887953466341 : Nat.Prime 26112887953466341 := by
  apply lucas_primality 26112887953466341 (2 : ZMod 26112887953466341)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (233, 1), (401, 1), (839, 1), (427069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (233, 1), (401, 1), (839, 1), (427069, 1)] : List FactorBlock).map factorBlockValue).prod) = 26112887953466341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_233
      · exact prime_oneHundredSixtySevenFI_401
      · exact prime_oneHundredSixtySevenFI_839
      · exact prime_oneHundredSixtySevenFI_427069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26112887953466341) ^ 13056443976733170 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 26112887953466341) ^ 8704295984488780 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 26112887953466341) ^ 5222577590693268 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 26112887953466341) ^ 2008683688728180 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 26112887953466341) ^ 112072480486980 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 26112887953466341) ^ 65119421330340 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 26112887953466341) ^ 31123823544060 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 26112887953466341) ^ 61144423860 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_65979949850570839 : Nat.Prime 65979949850570839 := by
  apply lucas_primality 65979949850570839 (3 : ZMod 65979949850570839)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (41, 1), (15777128132609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (41, 1), (15777128132609, 1)] : List FactorBlock).map factorBlockValue).prod) = 65979949850570839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_17
      · exact prime_oneHundredSixtySevenFI_41
      · exact prime_oneHundredSixtySevenFI_15777128132609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65979949850570839) ^ 32989974925285419 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 65979949850570839) ^ 21993316616856946 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 65979949850570839) ^ 3881173520621814 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 65979949850570839) ^ 1609267069526118 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 65979949850570839) ^ 4182 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_68750477765090267 : Nat.Prime 68750477765090267 := by
  apply lucas_primality 68750477765090267 (2 : ZMod 68750477765090267)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2729, 1), (12596276615077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2729, 1), (12596276615077, 1)] : List FactorBlock).map factorBlockValue).prod) = 68750477765090267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_2729
      · exact prime_oneHundredSixtySevenFI_12596276615077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 68750477765090267) ^ 34375238882545133 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 68750477765090267) ^ 25192553230154 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 68750477765090267) ^ 5458 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_105866668498681267 : Nat.Prime 105866668498681267 := by
  apply lucas_primality 105866668498681267 (2 : ZMod 105866668498681267)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1604040431798201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1604040431798201, 1)] : List FactorBlock).map factorBlockValue).prod) = 105866668498681267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_1604040431798201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 105866668498681267) ^ 52933334249340633 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 105866668498681267) ^ 35288889499560422 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 105866668498681267) ^ 9624242590789206 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 105866668498681267) ^ 66 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_126820703088853129 : Nat.Prime 126820703088853129 := by
  apply lucas_primality 126820703088853129 (7 : ZMod 126820703088853129)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (115001, 1), (15316376849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (115001, 1), (15316376849, 1)] : List FactorBlock).map factorBlockValue).prod) = 126820703088853129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_115001
      · exact prime_oneHundredSixtySevenFI_15316376849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 126820703088853129) ^ 63410351544426564 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 126820703088853129) ^ 42273567696284376 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 126820703088853129) ^ 1102779133128 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 126820703088853129) ^ 8280072 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_131086452514152809 : Nat.Prime 131086452514152809 := by
  apply lucas_primality 131086452514152809 (3 : ZMod 131086452514152809)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (16385806564269101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (16385806564269101, 1)] : List FactorBlock).map factorBlockValue).prod) = 131086452514152809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_16385806564269101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 131086452514152809) ^ 65543226257076404 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 131086452514152809) ^ 8 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_271517475994934063 : Nat.Prime 271517475994934063 := by
  apply lucas_primality 271517475994934063 (5 : ZMod 271517475994934063)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (39201719, 1), (3463081249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (39201719, 1), (3463081249, 1)] : List FactorBlock).map factorBlockValue).prod) = 271517475994934063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_39201719
      · exact prime_oneHundredSixtySevenFI_3463081249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 271517475994934063) ^ 135758737997467031 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 271517475994934063) ^ 6926162498 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 271517475994934063) ^ 78403438 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_300051194740345681 : Nat.Prime 300051194740345681 := by
  apply lucas_primality 300051194740345681 (7 : ZMod 300051194740345681)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (65800700600953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (65800700600953, 1)] : List FactorBlock).map factorBlockValue).prod) = 300051194740345681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_65800700600953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 300051194740345681) ^ 150025597370172840 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 300051194740345681) ^ 100017064913448560 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 300051194740345681) ^ 60010238948069136 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 300051194740345681) ^ 15792168144228720 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 300051194740345681) ^ 4560 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_515446556253363421 : Nat.Prime 515446556253363421 := by
  apply lucas_primality 515446556253363421 (2 : ZMod 515446556253363421)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (37, 1), (2377, 1), (13954151899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (37, 1), (2377, 1), (13954151899, 1)] : List FactorBlock).map factorBlockValue).prod) = 515446556253363421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_37
      · exact prime_oneHundredSixtySevenFI_2377
      · exact prime_oneHundredSixtySevenFI_13954151899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 515446556253363421) ^ 257723278126681710 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 515446556253363421) ^ 171815518751121140 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 515446556253363421) ^ 103089311250672684 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 515446556253363421) ^ 73635222321909060 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 515446556253363421) ^ 13930988006847660 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 515446556253363421) ^ 216847520510460 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 515446556253363421) ^ 36938580 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_604565947988332511 : Nat.Prime 604565947988332511 := by
  apply lucas_primality 604565947988332511 (11 : ZMod 604565947988332511)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (107, 1), (7644079, 1), (73915367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (107, 1), (7644079, 1), (73915367, 1)] : List FactorBlock).map factorBlockValue).prod) = 604565947988332511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_107
      · exact prime_oneHundredSixtySevenFI_7644079
      · exact prime_oneHundredSixtySevenFI_73915367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 604565947988332511) ^ 302282973994166255 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 604565947988332511) ^ 120913189597666502 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 604565947988332511) ^ 5650149046619930 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 604565947988332511) ^ 79089442690 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 604565947988332511) ^ 8179164530 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_635200010992087603 : Nat.Prime 635200010992087603 := by
  apply lucas_primality 635200010992087603 (2 : ZMod 635200010992087603)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (105866668498681267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (105866668498681267, 1)] : List FactorBlock).map factorBlockValue).prod) = 635200010992087603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_105866668498681267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 635200010992087603) ^ 317600005496043801 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 635200010992087603) ^ 211733336997362534 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 635200010992087603) ^ 6 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_772160947424672501 : Nat.Prime 772160947424672501 := by
  apply lucas_primality 772160947424672501 (2 : ZMod 772160947424672501)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 4), (43, 1), (277, 1), (383, 1), (67705013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 4), (43, 1), (277, 1), (383, 1), (67705013, 1)] : List FactorBlock).map factorBlockValue).prod) = 772160947424672501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_43
      · exact prime_oneHundredSixtySevenFI_277
      · exact prime_oneHundredSixtySevenFI_383
      · exact prime_oneHundredSixtySevenFI_67705013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 772160947424672501) ^ 386080473712336250 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 772160947424672501) ^ 154432189484934500 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 772160947424672501) ^ 17957231335457500 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 772160947424672501) ^ 2787584647742500 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 772160947424672501) ^ 2016086024607500 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 772160947424672501) ^ 11404782500 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1171597731500656063 : Nat.Prime 1171597731500656063 := by
  apply lucas_primality 1171597731500656063 (6 : ZMod 1171597731500656063)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (24593, 1), (2646637777463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (24593, 1), (2646637777463, 1)] : List FactorBlock).map factorBlockValue).prod) = 1171597731500656063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_24593
      · exact prime_oneHundredSixtySevenFI_2646637777463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1171597731500656063) ^ 585798865750328031 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1171597731500656063) ^ 390532577166885354 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1171597731500656063) ^ 47639479994334 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1171597731500656063) ^ 442674 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1650011466362166409 : Nat.Prime 1650011466362166409 := by
  apply lucas_primality 1650011466362166409 (11 : ZMod 1650011466362166409)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (68750477765090267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (68750477765090267, 1)] : List FactorBlock).map factorBlockValue).prod) = 1650011466362166409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_68750477765090267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1650011466362166409) ^ 825005733181083204 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1650011466362166409) ^ 550003822120722136 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1650011466362166409) ^ 24 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_2288749554141759119 : Nat.Prime 2288749554141759119 := by
  apply lucas_primality 2288749554141759119 (11 : ZMod 2288749554141759119)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (362137, 1), (3160060355807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (362137, 1), (3160060355807, 1)] : List FactorBlock).map factorBlockValue).prod) = 2288749554141759119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_362137
      · exact prime_oneHundredSixtySevenFI_3160060355807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 2288749554141759119) ^ 1144374777070879559 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2288749554141759119) ^ 6320120711614 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2288749554141759119) ^ 724274 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_2658311230442094251 : Nat.Prime 2658311230442094251 := by
  apply lucas_primality 2658311230442094251 (6 : ZMod 2658311230442094251)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (29, 1), (83, 1), (349, 1), (12657976939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (29, 1), (83, 1), (349, 1), (12657976939, 1)] : List FactorBlock).map factorBlockValue).prod) = 2658311230442094251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_29
      · exact prime_oneHundredSixtySevenFI_83
      · exact prime_oneHundredSixtySevenFI_349
      · exact prime_oneHundredSixtySevenFI_12657976939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2658311230442094251) ^ 1329155615221047125 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2658311230442094251) ^ 531662246088418850 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2658311230442094251) ^ 91665904498003250 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2658311230442094251) ^ 32027846149904750 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2658311230442094251) ^ 7616937623043250 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2658311230442094251) ^ 210010750 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_2984705945481708509 : Nat.Prime 2984705945481708509 := by
  apply lucas_primality 2984705945481708509 (2 : ZMod 2984705945481708509)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (16811, 1), (1530558781033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (16811, 1), (1530558781033, 1)] : List FactorBlock).map factorBlockValue).prod) = 2984705945481708509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_29
      · exact prime_oneHundredSixtySevenFI_16811
      · exact prime_oneHundredSixtySevenFI_1530558781033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2984705945481708509) ^ 1492352972740854254 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2984705945481708509) ^ 102920894671783052 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2984705945481708509) ^ 177544818599828 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2984705945481708509) ^ 1950076 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_3126934034869599323 : Nat.Prime 3126934034869599323 := by
  apply lucas_primality 3126934034869599323 (2 : ZMod 3126934034869599323)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5653, 1), (44053, 1), (6278187029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5653, 1), (44053, 1), (6278187029, 1)] : List FactorBlock).map factorBlockValue).prod) = 3126934034869599323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5653
      · exact prime_oneHundredSixtySevenFI_44053
      · exact prime_oneHundredSixtySevenFI_6278187029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3126934034869599323) ^ 1563467017434799661 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3126934034869599323) ^ 553145946377074 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3126934034869599323) ^ 70981182549874 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3126934034869599323) ^ 498063218 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_3784298292927673681 : Nat.Prime 3784298292927673681 := by
  apply lucas_primality 3784298292927673681 (7 : ZMod 3784298292927673681)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (262597, 1), (60046038431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (262597, 1), (60046038431, 1)] : List FactorBlock).map factorBlockValue).prod) = 3784298292927673681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_262597
      · exact prime_oneHundredSixtySevenFI_60046038431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3784298292927673681) ^ 1892149146463836840 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 3784298292927673681) ^ 1261432764309224560 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 3784298292927673681) ^ 756859658585534736 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 3784298292927673681) ^ 14411049223440 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 3784298292927673681) ^ 63023280 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_4823856924994351141 : Nat.Prime 4823856924994351141 := by
  apply lucas_primality 4823856924994351141 (2 : ZMod 4823856924994351141)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (19, 1), (13669, 1), (23812745533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (19, 1), (13669, 1), (23812745533, 1)] : List FactorBlock).map factorBlockValue).prod) = 4823856924994351141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_13669
      · exact prime_oneHundredSixtySevenFI_23812745533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4823856924994351141) ^ 2411928462497175570 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4823856924994351141) ^ 1607952308331450380 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4823856924994351141) ^ 964771384998870228 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4823856924994351141) ^ 371065917307257780 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4823856924994351141) ^ 253887206578650060 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4823856924994351141) ^ 352904888799060 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4823856924994351141) ^ 202574580 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_5239347761619341057 : Nat.Prime 5239347761619341057 := by
  apply lucas_primality 5239347761619341057 (3 : ZMod 5239347761619341057)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (37, 1), (53, 1), (877, 1), (19213, 1), (619391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (37, 1), (53, 1), (877, 1), (19213, 1), (619391, 1)] : List FactorBlock).map factorBlockValue).prod) = 5239347761619341057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_37
      · exact prime_oneHundredSixtySevenFI_53
      · exact prime_oneHundredSixtySevenFI_877
      · exact prime_oneHundredSixtySevenFI_19213
      · exact prime_oneHundredSixtySevenFI_619391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5239347761619341057) ^ 2619673880809670528 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5239347761619341057) ^ 141603993557279488 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5239347761619341057) ^ 98855618143761152 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5239347761619341057) ^ 5974170765814528 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5239347761619341057) ^ 272698056608512 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5239347761619341057) ^ 8458869698816 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_5675089554123048359 : Nat.Prime 5675089554123048359 := by
  apply lucas_primality 5675089554123048359 (11 : ZMod 5675089554123048359)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2753, 1), (6714217, 1), (11808583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2753, 1), (6714217, 1), (11808583, 1)] : List FactorBlock).map factorBlockValue).prod) = 5675089554123048359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_2753
      · exact prime_oneHundredSixtySevenFI_6714217
      · exact prime_oneHundredSixtySevenFI_11808583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5675089554123048359) ^ 2837544777061524179 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 5675089554123048359) ^ 436545350317157566 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 5675089554123048359) ^ 2061420106837286 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 5675089554123048359) ^ 845234753974 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 5675089554123048359) ^ 480590224426 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_8556498482329549651 : Nat.Prime 8556498482329549651 := by
  apply lucas_primality 8556498482329549651 (2 : ZMod 8556498482329549651)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (97, 1), (3361, 1), (367819, 1), (475697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (97, 1), (3361, 1), (367819, 1), (475697, 1)] : List FactorBlock).map factorBlockValue).prod) = 8556498482329549651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_97
      · exact prime_oneHundredSixtySevenFI_3361
      · exact prime_oneHundredSixtySevenFI_367819
      · exact prime_oneHundredSixtySevenFI_475697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8556498482329549651) ^ 4278249241164774825 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8556498482329549651) ^ 2852166160776516550 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8556498482329549651) ^ 1711299696465909930 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8556498482329549651) ^ 88211324560098450 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8556498482329549651) ^ 2545819244965650 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8556498482329549651) ^ 23262796327350 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8556498482329549651) ^ 17987287038450 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_22245829761113316601 : Nat.Prime 22245829761113316601 := by
  apply lucas_primality 22245829761113316601 (14 : ZMod 22245829761113316601)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (11, 1), (17, 1), (37, 1), (5358633174619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (11, 1), (17, 1), (37, 1), (5358633174619, 1)] : List FactorBlock).map factorBlockValue).prod) = 22245829761113316601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_17
      · exact prime_oneHundredSixtySevenFI_37
      · exact prime_oneHundredSixtySevenFI_5358633174619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 22245829761113316601) ^ 11122914880556658300 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (14 : ZMod 22245829761113316601) ^ 7415276587037772200 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (14 : ZMod 22245829761113316601) ^ 4449165952222663320 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (14 : ZMod 22245829761113316601) ^ 2022348160101210600 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (14 : ZMod 22245829761113316601) ^ 1308578221241959800 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (14 : ZMod 22245829761113316601) ^ 601238642192251800 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (14 : ZMod 22245829761113316601) ^ 4151400 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_25670109408545182661 : Nat.Prime 25670109408545182661 := by
  apply lucas_primality 25670109408545182661 (2 : ZMod 25670109408545182661)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (6967, 1), (184226420328299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (6967, 1), (184226420328299, 1)] : List FactorBlock).map factorBlockValue).prod) = 25670109408545182661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_6967
      · exact prime_oneHundredSixtySevenFI_184226420328299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25670109408545182661) ^ 12835054704272591330 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25670109408545182661) ^ 5134021881709036532 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25670109408545182661) ^ 3684528406565980 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25670109408545182661) ^ 139340 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_86590336453694386757 : Nat.Prime 86590336453694386757 := by
  apply lucas_primality 86590336453694386757 (2 : ZMod 86590336453694386757)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (829, 1), (26112887953466341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (829, 1), (26112887953466341, 1)] : List FactorBlock).map factorBlockValue).prod) = 86590336453694386757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_829
      · exact prime_oneHundredSixtySevenFI_26112887953466341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 86590336453694386757) ^ 43295168226847193378 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 86590336453694386757) ^ 104451551813865364 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 86590336453694386757) ^ 3316 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_112402268579530693921 : Nat.Prime 112402268579530693921 := by
  apply lucas_primality 112402268579530693921 (7 : ZMod 112402268579530693921)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (13, 1), (31, 1), (137, 1), (3169, 1), (1338400181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (13, 1), (31, 1), (137, 1), (3169, 1), (1338400181, 1)] : List FactorBlock).map factorBlockValue).prod) = 112402268579530693921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_31
      · exact prime_oneHundredSixtySevenFI_137
      · exact prime_oneHundredSixtySevenFI_3169
      · exact prime_oneHundredSixtySevenFI_1338400181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 112402268579530693921) ^ 56201134289765346960 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 112402268579530693921) ^ 37467422859843564640 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 112402268579530693921) ^ 22480453715906138784 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 112402268579530693921) ^ 8646328352271591840 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 112402268579530693921) ^ 3625879631597764320 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 112402268579530693921) ^ 820454515179056160 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 112402268579530693921) ^ 35469317948731680 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 112402268579530693921) ^ 83982556320 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_118470698322124585631 : Nat.Prime 118470698322124585631 := by
  apply lucas_primality 118470698322124585631 (41 : ZMod 118470698322124585631)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (59, 1), (139, 1), (1153, 1), (6257, 1), (4656721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (59, 1), (139, 1), (1153, 1), (6257, 1), (4656721, 1)] : List FactorBlock).map factorBlockValue).prod) = 118470698322124585631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_43
      · exact prime_oneHundredSixtySevenFI_59
      · exact prime_oneHundredSixtySevenFI_139
      · exact prime_oneHundredSixtySevenFI_1153
      · exact prime_oneHundredSixtySevenFI_6257
      · exact prime_oneHundredSixtySevenFI_4656721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (41 : ZMod 118470698322124585631) ^ 59235349161062292815 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (41 : ZMod 118470698322124585631) ^ 23694139664424917126 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (41 : ZMod 118470698322124585631) ^ 2755132519119176410 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (41 : ZMod 118470698322124585631) ^ 2007977937663128570 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (41 : ZMod 118470698322124585631) ^ 852307182173558170 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (41 : ZMod 118470698322124585631) ^ 102749955179639710 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (41 : ZMod 118470698322124585631) ^ 18934105533342590 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (41 : ZMod 118470698322124585631) ^ 25440798004030 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_261939254420876962147 : Nat.Prime 261939254420876962147 := by
  apply lucas_primality 261939254420876962147 (2 : ZMod 261939254420876962147)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (19, 1), (23, 1), (1783, 1), (295259, 1), (3872731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (19, 1), (23, 1), (1783, 1), (295259, 1), (3872731, 1)] : List FactorBlock).map factorBlockValue).prod) = 261939254420876962147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_23
      · exact prime_oneHundredSixtySevenFI_1783
      · exact prime_oneHundredSixtySevenFI_295259
      · exact prime_oneHundredSixtySevenFI_3872731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 261939254420876962147) ^ 130969627210438481073 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 261939254420876962147) ^ 87313084806958987382 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 261939254420876962147) ^ 37419893488696708878 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 261939254420876962147) ^ 13786276548467208534 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 261939254420876962147) ^ 11388663235690302702 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 261939254420876962147) ^ 146909284588265262 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 261939254420876962147) ^ 887150787684294 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 261939254420876962147) ^ 67636831584966 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_294419161081523020111 : Nat.Prime 294419161081523020111 := by
  apply lucas_primality 294419161081523020111 (6 : ZMod 294419161081523020111)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (79, 1), (131, 1), (948301481887213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (79, 1), (131, 1), (948301481887213, 1)] : List FactorBlock).map factorBlockValue).prod) = 294419161081523020111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_79
      · exact prime_oneHundredSixtySevenFI_131
      · exact prime_oneHundredSixtySevenFI_948301481887213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 294419161081523020111) ^ 147209580540761510055 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 294419161081523020111) ^ 98139720360507673370 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 294419161081523020111) ^ 58883832216304604022 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 294419161081523020111) ^ 3726824823816747090 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 294419161081523020111) ^ 2247474512072694810 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 294419161081523020111) ^ 310470 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_435603027119611931977 : Nat.Prime 435603027119611931977 := by
  apply lucas_primality 435603027119611931977 (7 : ZMod 435603027119611931977)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (1650011466362166409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (1650011466362166409, 1)] : List FactorBlock).map factorBlockValue).prod) = 435603027119611931977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_1650011466362166409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 435603027119611931977) ^ 217801513559805965988 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 435603027119611931977) ^ 145201009039870643992 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 435603027119611931977) ^ 39600275192691993816 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 435603027119611931977) ^ 264 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_569959575229501383097 : Nat.Prime 569959575229501383097 := by
  apply lucas_primality 569959575229501383097 (5 : ZMod 569959575229501383097)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (79, 1), (953, 1), (105145711896089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (79, 1), (953, 1), (105145711896089, 1)] : List FactorBlock).map factorBlockValue).prod) = 569959575229501383097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_79
      · exact prime_oneHundredSixtySevenFI_953
      · exact prime_oneHundredSixtySevenFI_105145711896089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 569959575229501383097) ^ 284979787614750691548 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 569959575229501383097) ^ 189986525076500461032 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 569959575229501383097) ^ 7214678167462042824 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 569959575229501383097) ^ 598068809264954232 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 569959575229501383097) ^ 5420664 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_710824189932747513787 : Nat.Prime 710824189932747513787 := by
  apply lucas_primality 710824189932747513787 (2 : ZMod 710824189932747513787)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (118470698322124585631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (118470698322124585631, 1)] : List FactorBlock).map factorBlockValue).prod) = 710824189932747513787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_118470698322124585631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 710824189932747513787) ^ 355412094966373756893 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 710824189932747513787) ^ 236941396644249171262 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 710824189932747513787) ^ 6 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1047757017683507848589 : Nat.Prime 1047757017683507848589 := by
  apply lucas_primality 1047757017683507848589 (2 : ZMod 1047757017683507848589)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (261939254420876962147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (261939254420876962147, 1)] : List FactorBlock).map factorBlockValue).prod) = 1047757017683507848589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_261939254420876962147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1047757017683507848589) ^ 523878508841753924294 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1047757017683507848589) ^ 4 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_2843296759730990055149 : Nat.Prime 2843296759730990055149 := by
  apply lucas_primality 2843296759730990055149 (2 : ZMod 2843296759730990055149)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (710824189932747513787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (710824189932747513787, 1)] : List FactorBlock).map factorBlockValue).prod) = 2843296759730990055149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_710824189932747513787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2843296759730990055149) ^ 1421648379865495027574 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2843296759730990055149) ^ 4 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_3705955554361234879631 : Nat.Prime 3705955554361234879631 := by
  apply lucas_primality 3705955554361234879631 (11 : ZMod 3705955554361234879631)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (31, 1), (22523299, 1), (27935272333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (31, 1), (22523299, 1), (27935272333, 1)] : List FactorBlock).map factorBlockValue).prod) = 3705955554361234879631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_31
      · exact prime_oneHundredSixtySevenFI_22523299
      · exact prime_oneHundredSixtySevenFI_27935272333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3705955554361234879631) ^ 1852977777180617439815 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 3705955554361234879631) ^ 741191110872246975926 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 3705955554361234879631) ^ 195050292334801835770 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 3705955554361234879631) ^ 119546953366491447730 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 3705955554361234879631) ^ 164538754041370 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 3705955554361234879631) ^ 132662231110 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_4856111556718493900779 : Nat.Prime 4856111556718493900779 := by
  apply lucas_primality 4856111556718493900779 (2 : ZMod 4856111556718493900779)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (257, 1), (317, 1), (91141993011103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (257, 1), (317, 1), (91141993011103, 1)] : List FactorBlock).map factorBlockValue).prod) = 4856111556718493900779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_109
      · exact prime_oneHundredSixtySevenFI_257
      · exact prime_oneHundredSixtySevenFI_317
      · exact prime_oneHundredSixtySevenFI_91141993011103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4856111556718493900779) ^ 2428055778359246950389 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4856111556718493900779) ^ 1618703852239497966926 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4856111556718493900779) ^ 44551482171729301842 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4856111556718493900779) ^ 18895375707075851754 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4856111556718493900779) ^ 15318963901320170034 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4856111556718493900779) ^ 53280726 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_5631830709239040296303 : Nat.Prime 5631830709239040296303 := by
  apply lucas_primality 5631830709239040296303 (5 : ZMod 5631830709239040296303)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (73, 1), (79, 1), (383, 1), (3517, 1), (27884004871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (73, 1), (79, 1), (383, 1), (3517, 1), (27884004871, 1)] : List FactorBlock).map factorBlockValue).prod) = 5631830709239040296303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_13
      · exact prime_oneHundredSixtySevenFI_73
      · exact prime_oneHundredSixtySevenFI_79
      · exact prime_oneHundredSixtySevenFI_383
      · exact prime_oneHundredSixtySevenFI_3517
      · exact prime_oneHundredSixtySevenFI_27884004871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5631830709239040296303) ^ 2815915354619520148151 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5631830709239040296303) ^ 433217746864541561254 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5631830709239040296303) ^ 77148365879986853374 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5631830709239040296303) ^ 71288996319481522738 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5631830709239040296303) ^ 14704518823078434194 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5631830709239040296303) ^ 1601316664554745606 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5631830709239040296303) ^ 201973523362 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_8252479623729149909209 : Nat.Prime 8252479623729149909209 := by
  apply lucas_primality 8252479623729149909209 (11 : ZMod 8252479623729149909209)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (36860771, 1), (3109478435809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (36860771, 1), (3109478435809, 1)] : List FactorBlock).map factorBlockValue).prod) = 8252479623729149909209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_36860771
      · exact prime_oneHundredSixtySevenFI_3109478435809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 8252479623729149909209) ^ 4126239811864574954604 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 8252479623729149909209) ^ 2750826541243049969736 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 8252479623729149909209) ^ 223882447378248 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 8252479623729149909209) ^ 2653975512 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_8538703069776437168953 : Nat.Prime 8538703069776437168953 := by
  apply lucas_primality 8538703069776437168953 (10 : ZMod 8538703069776437168953)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (41, 1), (2851, 1), (14009, 1), (42821, 1), (461257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (41, 1), (2851, 1), (14009, 1), (42821, 1), (461257, 1)] : List FactorBlock).map factorBlockValue).prod) = 8538703069776437168953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_41
      · exact prime_oneHundredSixtySevenFI_2851
      · exact prime_oneHundredSixtySevenFI_14009
      · exact prime_oneHundredSixtySevenFI_42821
      · exact prime_oneHundredSixtySevenFI_461257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 8538703069776437168953) ^ 4269351534888218584476 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 8538703069776437168953) ^ 2846234356592145722984 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 8538703069776437168953) ^ 776245733616039742632 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 8538703069776437168953) ^ 208261050482352126072 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 8538703069776437168953) ^ 2994985292801275752 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 8538703069776437168953) ^ 609515530714286328 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 8538703069776437168953) ^ 199404569481713112 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 8538703069776437168953) ^ 18511812438134136 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_10154753602210533956201 : Nat.Prime 10154753602210533956201 := by
  apply lucas_primality 10154753602210533956201 (3 : ZMod 10154753602210533956201)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (11, 1), (17, 1), (271517475994934063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (11, 1), (17, 1), (271517475994934063, 1)] : List FactorBlock).map factorBlockValue).prod) = 10154753602210533956201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_17
      · exact prime_oneHundredSixtySevenFI_271517475994934063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10154753602210533956201) ^ 5077376801105266978100 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 10154753602210533956201) ^ 2030950720442106791240 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 10154753602210533956201) ^ 923159418382775814200 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 10154753602210533956201) ^ 597338447188854938600 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 10154753602210533956201) ^ 37400 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_22235733326167409277787 : Nat.Prime 22235733326167409277787 := by
  apply lucas_primality 22235733326167409277787 (2 : ZMod 22235733326167409277787)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3705955554361234879631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3705955554361234879631, 1)] : List FactorBlock).map factorBlockValue).prod) = 22235733326167409277787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_3705955554361234879631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 22235733326167409277787) ^ 11117866663083704638893 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 22235733326167409277787) ^ 7411911108722469759262 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 22235733326167409277787) ^ 6 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_24432070845249026081449 : Nat.Prime 24432070845249026081449 := by
  apply lucas_primality 24432070845249026081449 (11 : ZMod 24432070845249026081449)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (292069, 1), (395741, 1), (8807497463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (292069, 1), (395741, 1), (8807497463, 1)] : List FactorBlock).map factorBlockValue).prod) = 24432070845249026081449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_292069
      · exact prime_oneHundredSixtySevenFI_395741
      · exact prime_oneHundredSixtySevenFI_8807497463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 24432070845249026081449) ^ 12216035422624513040724 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 24432070845249026081449) ^ 8144023615083008693816 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 24432070845249026081449) ^ 83651708484121992 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 24432070845249026081449) ^ 61737527436502728 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 24432070845249026081449) ^ 2774008275096 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_26381874201639384718819 : Nat.Prime 26381874201639384718819 := by
  apply lucas_primality 26381874201639384718819 (3 : ZMod 26381874201639384718819)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 3), (163, 1), (18253, 1), (370112051189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 3), (163, 1), (18253, 1), (370112051189, 1)] : List FactorBlock).map factorBlockValue).prod) = 26381874201639384718819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_163
      · exact prime_oneHundredSixtySevenFI_18253
      · exact prime_oneHundredSixtySevenFI_370112051189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26381874201639384718819) ^ 13190937100819692359409 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 26381874201639384718819) ^ 8793958067213128239606 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 26381874201639384718819) ^ 2398352200149034974438 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 26381874201639384718819) ^ 161851988967112789686 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 26381874201639384718819) ^ 1445344557148928106 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 26381874201639384718819) ^ 71280775962 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_28082904002279668065521 : Nat.Prime 28082904002279668065521 := by
  apply lucas_primality 28082904002279668065521 (3 : ZMod 28082904002279668065521)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (67, 1), (5239347761619341057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (67, 1), (5239347761619341057, 1)] : List FactorBlock).map factorBlockValue).prod) = 28082904002279668065521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_67
      · exact prime_oneHundredSixtySevenFI_5239347761619341057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 28082904002279668065521) ^ 14041452001139834032760 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 28082904002279668065521) ^ 5616580800455933613104 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 28082904002279668065521) ^ 419147820929547284560 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 28082904002279668065521) ^ 5360 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_28903267867948606355017 : Nat.Prime 28903267867948606355017 := by
  apply lucas_primality 28903267867948606355017 (13 : ZMod 28903267867948606355017)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (426582223, 1), (2823143494733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (426582223, 1), (2823143494733, 1)] : List FactorBlock).map factorBlockValue).prod) = 28903267867948606355017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_426582223
      · exact prime_oneHundredSixtySevenFI_2823143494733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 28903267867948606355017) ^ 14451633933974303177508 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 28903267867948606355017) ^ 9634422622649535451672 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 28903267867948606355017) ^ 67755443873592 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (13 : ZMod 28903267867948606355017) ^ 10237973352 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_49248427150679813659403 : Nat.Prime 49248427150679813659403 := by
  apply lucas_primality 49248427150679813659403 (2 : ZMod 49248427150679813659403)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4339, 1), (5675089554123048359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4339, 1), (5675089554123048359, 1)] : List FactorBlock).map factorBlockValue).prod) = 49248427150679813659403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_4339
      · exact prime_oneHundredSixtySevenFI_5675089554123048359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 49248427150679813659403) ^ 24624213575339906829701 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 49248427150679813659403) ^ 11350179108246096718 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 49248427150679813659403) ^ 8678 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_58511030951792460188087 : Nat.Prime 58511030951792460188087 := by
  apply lucas_primality 58511030951792460188087 (10 : ZMod 58511030951792460188087)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (163, 1), (1049, 1), (7439038837657943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (163, 1), (1049, 1), (7439038837657943, 1)] : List FactorBlock).map factorBlockValue).prod) = 58511030951792460188087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_23
      · exact prime_oneHundredSixtySevenFI_163
      · exact prime_oneHundredSixtySevenFI_1049
      · exact prime_oneHundredSixtySevenFI_7439038837657943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 58511030951792460188087) ^ 29255515475896230094043 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 58511030951792460188087) ^ 2543957867469237399482 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 58511030951792460188087) ^ 358963380072346381522 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 58511030951792460188087) ^ 55777913204759256614 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 58511030951792460188087) ^ 7865402 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_186321862066816788523907 : Nat.Prime 186321862066816788523907 := by
  apply lucas_primality 186321862066816788523907 (2 : ZMod 186321862066816788523907)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (25579, 1), (1135951, 1), (188600021821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (25579, 1), (1135951, 1), (188600021821, 1)] : List FactorBlock).map factorBlockValue).prod) = 186321862066816788523907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_17
      · exact prime_oneHundredSixtySevenFI_25579
      · exact prime_oneHundredSixtySevenFI_1135951
      · exact prime_oneHundredSixtySevenFI_188600021821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 186321862066816788523907) ^ 93160931033408394261953 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 186321862066816788523907) ^ 10960109533342164030818 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 186321862066816788523907) ^ 7284173035177950214 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 186321862066816788523907) ^ 164022798577418206 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 186321862066816788523907) ^ 987920681386 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_451166473145920289829023 : Nat.Prime 451166473145920289829023 := by
  apply lucas_primality 451166473145920289829023 (7 : ZMod 451166473145920289829023)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (79, 1), (179, 1), (191, 1), (11931506822380883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (79, 1), (179, 1), (191, 1), (11931506822380883, 1)] : List FactorBlock).map factorBlockValue).prod) = 451166473145920289829023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_79
      · exact prime_oneHundredSixtySevenFI_179
      · exact prime_oneHundredSixtySevenFI_191
      · exact prime_oneHundredSixtySevenFI_11931506822380883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 451166473145920289829023) ^ 225583236572960144914511 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 451166473145920289829023) ^ 64452353306560041404146 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 451166473145920289829023) ^ 5710968014505320124418 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 451166473145920289829023) ^ 2520483090200672010218 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 451166473145920289829023) ^ 2362128131654032931042 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 451166473145920289829023) ^ 37813034 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_1028963626649701353413821 : Nat.Prime 1028963626649701353413821 := by
  apply lucas_primality 1028963626649701353413821 (6 : ZMod 1028963626649701353413821)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (2111, 1), (19391, 1), (139649401306699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (2111, 1), (19391, 1), (139649401306699, 1)] : List FactorBlock).map factorBlockValue).prod) = 1028963626649701353413821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_2111
      · exact prime_oneHundredSixtySevenFI_19391
      · exact prime_oneHundredSixtySevenFI_139649401306699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1028963626649701353413821) ^ 514481813324850676706910 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1028963626649701353413821) ^ 342987875549900451137940 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1028963626649701353413821) ^ 205792725329940270682764 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1028963626649701353413821) ^ 487429477332876055620 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1028963626649701353413821) ^ 53063979508519486020 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1028963626649701353413821) ^ 7368192180 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_2236301305332223466319289 : Nat.Prime 2236301305332223466319289 := by
  apply lucas_primality 2236301305332223466319289 (11 : ZMod 2236301305332223466319289)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13967, 1), (21239707, 1), (314099627273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13967, 1), (21239707, 1), (314099627273, 1)] : List FactorBlock).map factorBlockValue).prod) = 2236301305332223466319289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_13967
      · exact prime_oneHundredSixtySevenFI_21239707
      · exact prime_oneHundredSixtySevenFI_314099627273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2236301305332223466319289) ^ 1118150652666111733159644 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2236301305332223466319289) ^ 745433768444074488773096 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2236301305332223466319289) ^ 160113217250105496264 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2236301305332223466319289) ^ 105288707858927784 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2236301305332223466319289) ^ 7119719704056 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_6519351812619162799881043 : Nat.Prime 6519351812619162799881043 := by
  apply lucas_primality 6519351812619162799881043 (2 : ZMod 6519351812619162799881043)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (10154753602210533956201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (10154753602210533956201, 1)] : List FactorBlock).map factorBlockValue).prod) = 6519351812619162799881043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_107
      · exact prime_oneHundredSixtySevenFI_10154753602210533956201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6519351812619162799881043) ^ 3259675906309581399940521 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6519351812619162799881043) ^ 2173117270873054266627014 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6519351812619162799881043) ^ 60928521613263203737206 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6519351812619162799881043) ^ 642 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_29964876255148178083836301 : Nat.Prime 29964876255148178083836301 := by
  apply lucas_primality 29964876255148178083836301 (14 : ZMod 29964876255148178083836301)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (17, 1), (233, 1), (5952911, 1), (4236010245151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (17, 1), (233, 1), (5952911, 1), (4236010245151, 1)] : List FactorBlock).map factorBlockValue).prod) = 29964876255148178083836301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_17
      · exact prime_oneHundredSixtySevenFI_233
      · exact prime_oneHundredSixtySevenFI_5952911
      · exact prime_oneHundredSixtySevenFI_4236010245151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 29964876255148178083836301) ^ 14982438127574089041918150 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (14 : ZMod 29964876255148178083836301) ^ 9988292085049392694612100 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (14 : ZMod 29964876255148178083836301) ^ 5992975251029635616767260 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (14 : ZMod 29964876255148178083836301) ^ 1762639779714598710813900 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (14 : ZMod 29964876255148178083836301) ^ 128604619120807631261100 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (14 : ZMod 29964876255148178083836301) ^ 5033650974312933300 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (14 : ZMod 29964876255148178083836301) ^ 7073844141300 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_48191010408877555624700363 : Nat.Prime 48191010408877555624700363 := by
  apply lucas_primality 48191010408877555624700363 (2 : ZMod 48191010408877555624700363)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4281649, 1), (190457623, 1), (29547899603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4281649, 1), (190457623, 1), (29547899603, 1)] : List FactorBlock).map factorBlockValue).prod) = 48191010408877555624700363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_4281649
      · exact prime_oneHundredSixtySevenFI_190457623
      · exact prime_oneHundredSixtySevenFI_29547899603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 48191010408877555624700363) ^ 24095505204438777812350181 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 48191010408877555624700363) ^ 11255245446060047338 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 48191010408877555624700363) ^ 253027469574570694 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 48191010408877555624700363) ^ 1630945382120654 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_110547911335482276256661471 : Nat.Prime 110547911335482276256661471 := by
  apply lucas_primality 110547911335482276256661471 (11 : ZMod 110547911335482276256661471)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3343, 1), (9739, 1), (10627, 1), (31951343081293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3343, 1), (9739, 1), (10627, 1), (31951343081293, 1)] : List FactorBlock).map factorBlockValue).prod) = 110547911335482276256661471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_3343
      · exact prime_oneHundredSixtySevenFI_9739
      · exact prime_oneHundredSixtySevenFI_10627
      · exact prime_oneHundredSixtySevenFI_31951343081293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 110547911335482276256661471) ^ 55273955667741138128330735 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 110547911335482276256661471) ^ 22109582267096455251332294 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 110547911335482276256661471) ^ 33068474823656080244290 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 110547911335482276256661471) ^ 11351053633379430768730 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 110547911335482276256661471) ^ 10402551174883059777610 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 110547911335482276256661471) ^ 3459883080790 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_125677001683750060722086179 : Nat.Prime 125677001683750060722086179 := by
  apply lucas_primality 125677001683750060722086179 (3 : ZMod 125677001683750060722086179)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (337, 1), (834131, 1), (37292587, 1), (1998103067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (337, 1), (834131, 1), (37292587, 1), (1998103067, 1)] : List FactorBlock).map factorBlockValue).prod) = 125677001683750060722086179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_337
      · exact prime_oneHundredSixtySevenFI_834131
      · exact prime_oneHundredSixtySevenFI_37292587
      · exact prime_oneHundredSixtySevenFI_1998103067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 125677001683750060722086179) ^ 62838500841875030361043089 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 125677001683750060722086179) ^ 41892333894583353574028726 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 125677001683750060722086179) ^ 372928788379080298878594 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 125677001683750060722086179) ^ 150668182436272073238 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 125677001683750060722086179) ^ 3370026372365909094 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 125677001683750060722086179) ^ 62898157637305734 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_187145563644712175729286623 : Nat.Prime 187145563644712175729286623 := by
  apply lucas_primality 187145563644712175729286623 (5 : ZMod 187145563644712175729286623)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10369, 1), (49057, 1), (3709117, 1), (49595371451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10369, 1), (49057, 1), (3709117, 1), (49595371451, 1)] : List FactorBlock).map factorBlockValue).prod) = 187145563644712175729286623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_10369
      · exact prime_oneHundredSixtySevenFI_49057
      · exact prime_oneHundredSixtySevenFI_3709117
      · exact prime_oneHundredSixtySevenFI_49595371451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 187145563644712175729286623) ^ 93572781822356087864643311 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 187145563644712175729286623) ^ 18048564340313644105438 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 187145563644712175729286623) ^ 3814859523507596790046 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 187145563644712175729286623) ^ 50455556846740659766 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 187145563644712175729286623) ^ 3773448170049722 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_192622994775776922335997451 : Nat.Prime 192622994775776922335997451 := by
  apply lucas_primality 192622994775776922335997451 (2 : ZMod 192622994775776922335997451)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (802297, 1), (148792487, 1), (10757236097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (802297, 1), (148792487, 1), (10757236097, 1)] : List FactorBlock).map factorBlockValue).prod) = 192622994775776922335997451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_802297
      · exact prime_oneHundredSixtySevenFI_148792487
      · exact prime_oneHundredSixtySevenFI_10757236097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 192622994775776922335997451) ^ 96311497387888461167998725 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 192622994775776922335997451) ^ 64207664925258974111999150 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 192622994775776922335997451) ^ 38524598955155384467199490 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 192622994775776922335997451) ^ 240089386817820485850 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 192622994775776922335997451) ^ 1294574737337221350 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 192622994775776922335997451) ^ 17906364891395850 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_204176390532752166902168963 : Nat.Prime 204176390532752166902168963 := by
  apply lucas_primality 204176390532752166902168963 (2 : ZMod 204176390532752166902168963)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18127, 1), (5631830709239040296303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18127, 1), (5631830709239040296303, 1)] : List FactorBlock).map factorBlockValue).prod) = 204176390532752166902168963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_18127
      · exact prime_oneHundredSixtySevenFI_5631830709239040296303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 204176390532752166902168963) ^ 102088195266376083451084481 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 204176390532752166902168963) ^ 11263661418478080592606 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 204176390532752166902168963) ^ 36254 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_311417302279450071599995879 : Nat.Prime 311417302279450071599995879 := by
  apply lucas_primality 311417302279450071599995879 (3 : ZMod 311417302279450071599995879)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1699, 1), (7573, 1), (155681651, 1), (8637170023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1699, 1), (7573, 1), (155681651, 1), (8637170023, 1)] : List FactorBlock).map factorBlockValue).prod) = 311417302279450071599995879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_1699
      · exact prime_oneHundredSixtySevenFI_7573
      · exact prime_oneHundredSixtySevenFI_155681651
      · exact prime_oneHundredSixtySevenFI_8637170023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 311417302279450071599995879) ^ 155708651139725035799997939 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 311417302279450071599995879) ^ 103805767426483357199998626 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 311417302279450071599995879) ^ 183294468675367905591522 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 311417302279450071599995879) ^ 41122052327934777710286 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 311417302279450071599995879) ^ 2000346863481362178 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 311417302279450071599995879) ^ 36055478987929386 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_712774619657658286622373239 : Nat.Prime 712774619657658286622373239 := by
  apply lucas_primality 712774619657658286622373239 (7 : ZMod 712774619657658286622373239)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (74377, 1), (435603027119611931977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (74377, 1), (435603027119611931977, 1)] : List FactorBlock).map factorBlockValue).prod) = 712774619657658286622373239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_74377
      · exact prime_oneHundredSixtySevenFI_435603027119611931977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 712774619657658286622373239) ^ 356387309828829143311186619 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 712774619657658286622373239) ^ 64797692696150753329306658 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 712774619657658286622373239) ^ 9583266596631462503494 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 712774619657658286622373239) ^ 1636294 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_731253961648782760719990323 : Nat.Prime 731253961648782760719990323 := by
  apply lucas_primality 731253961648782760719990323 (2 : ZMod 731253961648782760719990323)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (79, 1), (43787, 1), (300151, 1), (407501, 1), (45482453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (79, 1), (43787, 1), (300151, 1), (407501, 1), (45482453, 1)] : List FactorBlock).map factorBlockValue).prod) = 731253961648782760719990323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_79
      · exact prime_oneHundredSixtySevenFI_43787
      · exact prime_oneHundredSixtySevenFI_300151
      · exact prime_oneHundredSixtySevenFI_407501
      · exact prime_oneHundredSixtySevenFI_45482453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 731253961648782760719990323) ^ 365626980824391380359995161 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 731253961648782760719990323) ^ 38487050613093829511578438 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 731253961648782760719990323) ^ 9256379261376996971139118 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 731253961648782760719990323) ^ 16700252624038704654806 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 731253961648782760719990323) ^ 2436286941068937837022 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 731253961648782760719990323) ^ 1794483845803526275322 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 731253961648782760719990323) ^ 16077715985300589674 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_2467982120564641817429967341 : Nat.Prime 2467982120564641817429967341 := by
  apply lucas_primality 2467982120564641817429967341 (2 : ZMod 2467982120564641817429967341)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (167, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (167, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 2467982120564641817429967341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_167
      · exact prime_oneHundredSixtySevenFI_171401
      · exact prime_oneHundredSixtySevenFI_714027719
      · exact prime_oneHundredSixtySevenFI_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2467982120564641817429967341) ^ 1233991060282320908714983670 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2467982120564641817429967341) ^ 493596424112928363485993468 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2467982120564641817429967341) ^ 14778336051285280343892020 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2467982120564641817429967341) ^ 14398878189535894291340 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2467982120564641817429967341) ^ 3456423406112391860 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2467982120564641817429967341) ^ 408766117314825460 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_4113303534274403029049945567 : Nat.Prime 4113303534274403029049945567 := by
  apply lucas_primality 4113303534274403029049945567 (5 : ZMod 4113303534274403029049945567)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (373, 1), (26381874201639384718819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (373, 1), (26381874201639384718819, 1)] : List FactorBlock).map factorBlockValue).prod) = 4113303534274403029049945567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_373
      · exact prime_oneHundredSixtySevenFI_26381874201639384718819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4113303534274403029049945567) ^ 2056651767137201514524972783 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 4113303534274403029049945567) ^ 373936684934036639004540506 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 4113303534274403029049945567) ^ 216489659698652791002628714 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 4113303534274403029049945567) ^ 11027623416285262812466342 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (5 : ZMod 4113303534274403029049945567) ^ 155914 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_4487240219208439668054486073 : Nat.Prime 4487240219208439668054486073 := by
  apply lucas_primality 4487240219208439668054486073 (11 : ZMod 4487240219208439668054486073)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (373, 1), (26381874201639384718819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (373, 1), (26381874201639384718819, 1)] : List FactorBlock).map factorBlockValue).prod) = 4487240219208439668054486073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_19
      · exact prime_oneHundredSixtySevenFI_373
      · exact prime_oneHundredSixtySevenFI_26381874201639384718819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4487240219208439668054486073) ^ 2243620109604219834027243036 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 4487240219208439668054486073) ^ 1495746739736146556018162024 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 4487240219208439668054486073) ^ 236170537853075772002867688 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 4487240219208439668054486073) ^ 12030134635947559431781464 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (11 : ZMod 4487240219208439668054486073) ^ 170088 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_4591594642910961520799939239 : Nat.Prime 4591594642910961520799939239 := by
  apply lucas_primality 4591594642910961520799939239 (6 : ZMod 4591594642910961520799939239)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (29, 1), (41, 1), (58511030951792460188087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (29, 1), (41, 1), (58511030951792460188087, 1)] : List FactorBlock).map factorBlockValue).prod) = 4591594642910961520799939239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_11
      · exact prime_oneHundredSixtySevenFI_29
      · exact prime_oneHundredSixtySevenFI_41
      · exact prime_oneHundredSixtySevenFI_58511030951792460188087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4591594642910961520799939239) ^ 2295797321455480760399969619 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4591594642910961520799939239) ^ 1530531547636987173599979746 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4591594642910961520799939239) ^ 417417694810087410981812658 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4591594642910961520799939239) ^ 158330849755550397268963422 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4591594642910961520799939239) ^ 111990113241730768799998518 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (6 : ZMod 4591594642910961520799939239) ^ 78474 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_4700918324885032033199937791 : Nat.Prime 4700918324885032033199937791 := by
  apply lucas_primality 4700918324885032033199937791 (7 : ZMod 4700918324885032033199937791)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (25163, 1), (29411, 1), (635200010992087603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (25163, 1), (29411, 1), (635200010992087603, 1)] : List FactorBlock).map factorBlockValue).prod) = 4700918324885032033199937791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_5
      · exact prime_oneHundredSixtySevenFI_25163
      · exact prime_oneHundredSixtySevenFI_29411
      · exact prime_oneHundredSixtySevenFI_635200010992087603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4700918324885032033199937791) ^ 2350459162442516016599968895 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 4700918324885032033199937791) ^ 940183664977006406639987558 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 4700918324885032033199937791) ^ 186818675232882884918330 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 4700918324885032033199937791) ^ 159835378765939003542890 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (7 : ZMod 4700918324885032033199937791) ^ 7400689930 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_9871928482258567269719869363 : Nat.Prime 9871928482258567269719869363 := by
  apply lucas_primality 9871928482258567269719869363 (2 : ZMod 9871928482258567269719869363)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (15939433, 1), (4097030813, 1), (25194668663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (15939433, 1), (4097030813, 1), (25194668663, 1)] : List FactorBlock).map factorBlockValue).prod) = 9871928482258567269719869363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_15939433
      · exact prime_oneHundredSixtySevenFI_4097030813
      · exact prime_oneHundredSixtySevenFI_25194668663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9871928482258567269719869363) ^ 4935964241129283634859934681 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9871928482258567269719869363) ^ 3290642827419522423239956454 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9871928482258567269719869363) ^ 619340003013819078114 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9871928482258567269719869363) ^ 2409532398666528474 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9871928482258567269719869363) ^ 391826088856494174 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_16453214137097612116199782273 : Nat.Prime 16453214137097612116199782273 := by
  apply lucas_primality 16453214137097612116199782273 (10 : ZMod 16453214137097612116199782273)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (7, 1), (742084921, 1), (2749455050663513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (7, 1), (742084921, 1), (2749455050663513, 1)] : List FactorBlock).map factorBlockValue).prod) = 16453214137097612116199782273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_7
      · exact prime_oneHundredSixtySevenFI_742084921
      · exact prime_oneHundredSixtySevenFI_2749455050663513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 16453214137097612116199782273) ^ 8226607068548806058099891136 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 16453214137097612116199782273) ^ 5484404712365870705399927424 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 16453214137097612116199782273) ^ 2350459162442516016599968896 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 16453214137097612116199782273) ^ 22171605528550568832 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (10 : ZMod 16453214137097612116199782273) ^ 5984172802944 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_65812856548390448464799129069 : Nat.Prime 65812856548390448464799129069 := by
  apply lucas_primality 65812856548390448464799129069 (2 : ZMod 65812856548390448464799129069)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (569251, 1), (28903267867948606355017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (569251, 1), (28903267867948606355017, 1)] : List FactorBlock).map factorBlockValue).prod) = 65812856548390448464799129069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_569251
      · exact prime_oneHundredSixtySevenFI_28903267867948606355017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 65812856548390448464799129069) ^ 32906428274195224232399564534 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 65812856548390448464799129069) ^ 115613071471794425420068 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 65812856548390448464799129069) ^ 2277004 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_65812856548390448464799129083 : Nat.Prime 65812856548390448464799129083 := by
  apply lucas_primality 65812856548390448464799129083 (3 : ZMod 65812856548390448464799129083)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (21059, 1), (8538703069776437168953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (21059, 1), (8538703069776437168953, 1)] : List FactorBlock).map factorBlockValue).prod) = 65812856548390448464799129083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_3
      · exact prime_oneHundredSixtySevenFI_61
      · exact prime_oneHundredSixtySevenFI_21059
      · exact prime_oneHundredSixtySevenFI_8538703069776437168953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65812856548390448464799129083) ^ 32906428274195224232399564541 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 65812856548390448464799129083) ^ 21937618849463482821599709694 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 65812856548390448464799129083) ^ 1078899287678531942045887362 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 65812856548390448464799129083) ^ 3125165323538176003836798 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (3 : ZMod 65812856548390448464799129083) ^ 7707594 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySevenFI_197438569645171345394397387269 : Nat.Prime 197438569645171345394397387269 := by
  apply lucas_primality 197438569645171345394397387269 (2 : ZMod 197438569645171345394397387269)
  · rw [← oneHundredSixtySevenFIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (193, 1), (1237, 1), (1787, 1), (3126934034869599323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (193, 1), (1237, 1), (1787, 1), (3126934034869599323, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySevenFI_2
      · exact prime_oneHundredSixtySevenFI_37
      · exact prime_oneHundredSixtySevenFI_193
      · exact prime_oneHundredSixtySevenFI_1237
      · exact prime_oneHundredSixtySevenFI_1787
      · exact prime_oneHundredSixtySevenFI_3126934034869599323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 197438569645171345394397387269) ^ 98719284822585672697198693634 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 197438569645171345394397387269) ^ 5336177557977603929578307764 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 197438569645171345394397387269) ^ 1022997770182234950230038276 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 197438569645171345394397387269) ^ 159610808120591225056101364 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 197438569645171345394397387269) ^ 110486049045982845771906764 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide
    · change (2 : ZMod 197438569645171345394397387269) ^ 63141264716 ≠ 1
      rw [← oneHundredSixtySevenFIFastPow_eq_pow]
      decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387200 : Nat.totient 197438569645171345394397387200 = 78502062976447111154002944000 := by
  rw [← show ((([(2, 6), (5, 2), (167, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_167, prime_oneHundredSixtySevenFI_171401, prime_oneHundredSixtySevenFI_714027719, prime_oneHundredSixtySevenFI_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387201 : Nat.totient 197438569645171345394397387201 = 99057783224609000314551705600 := by
  rw [← show ((([(3, 2), (7, 2), (11, 1), (31, 1), (499, 1), (434479, 1), (32059609, 1), (188891089, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_7, prime_oneHundredSixtySevenFI_11, prime_oneHundredSixtySevenFI_31, prime_oneHundredSixtySevenFI_499, prime_oneHundredSixtySevenFI_434479, prime_oneHundredSixtySevenFI_32059609, prime_oneHundredSixtySevenFI_188891089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387202 : Nat.totient 197438569645171345394397387202 = 97559249474715882858350795904 := by
  rw [← show ((([(2, 1), (137, 1), (223, 1), (178887827, 1), (18063245379444413, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_137, prime_oneHundredSixtySevenFI_223, prime_oneHundredSixtySevenFI_178887827, prime_oneHundredSixtySevenFI_18063245379444413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387203 : Nat.totient 197438569645171345394397387203 = 196725795025513687107775013688 := by
  rw [← show ((([(277, 1), (712774619657658286622373239, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_277, prime_oneHundredSixtySevenFI_712774619657658286622373239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387204 : Nat.totient 197438569645171345394397387204 = 65812740935318976670371432000 := by
  rw [← show ((([(2, 2), (3, 1), (569251, 1), (28903267867948606355017, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_569251, prime_oneHundredSixtySevenFI_28903267867948606355017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387205 : Nat.totient 197438569645171345394397387205 = 134652228648732353559548190720 := by
  rw [← show ((([(5, 1), (13, 1), (23, 1), (29, 1), (359621, 1), (282095273, 1), (44890242587, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_13, prime_oneHundredSixtySevenFI_23, prime_oneHundredSixtySevenFI_29, prime_oneHundredSixtySevenFI_359621, prime_oneHundredSixtySevenFI_282095273, prime_oneHundredSixtySevenFI_44890242587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387206 : Nat.totient 197438569645171345394397387206 = 91533670585779324740515697160 := by
  rw [← show ((([(2, 1), (19, 1), (47, 1), (110547911335482276256661471, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_19, prime_oneHundredSixtySevenFI_47, prime_oneHundredSixtySevenFI_110547911335482276256661471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387207 : Nat.totient 197438569645171345394397387207 = 131625713096780896929598258136 := by
  rw [← show ((([(3, 1), (65812856548390448464799129069, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_65812856548390448464799129069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387208 : Nat.totient 197438569645171345394397387208 = 84616504701762152193329754432 := by
  rw [← show ((([(2, 3), (7, 1), (3364987, 1), (1047757017683507848589, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_7, prime_oneHundredSixtySevenFI_3364987, prime_oneHundredSixtySevenFI_1047757017683507848589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387209 : Nat.totient 197438569645171345394397387209 = 197312892643487595333675299460 := by
  rw [← show ((([(1571, 1), (125677001683750060722086179, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_1571, prime_oneHundredSixtySevenFI_125677001683750060722086179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387210 : Nat.totient 197438569645171345394397387210 = 52650285238712358771839303184 := by
  rw [← show ((([(2, 1), (3, 3), (5, 1), (731253961648782760719990323, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_731253961648782760719990323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387211 : Nat.totient 197438569645171345394397387211 = 185053479970089813598849390080 := by
  rw [← show ((([(17, 1), (241, 1), (48191010408877555624700363, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_17, prime_oneHundredSixtySevenFI_241, prime_oneHundredSixtySevenFI_48191010408877555624700363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387212 : Nat.totient 197438569645171345394397387212 = 89744804384168793361089721440 := by
  rw [← show ((([(2, 2), (11, 1), (4487240219208439668054486073, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_11, prime_oneHundredSixtySevenFI_4487240219208439668054486073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387213 : Nat.totient 197438569645171345394397387213 = 131625696591821649471282489888 := by
  rw [← show ((([(3, 1), (7974919, 1), (8252479623729149909209, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_7974919, prime_oneHundredSixtySevenFI_8252479623729149909209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387214 : Nat.totient 197438569645171345394397387214 = 98718833656112526776908645776 := by
  rw [← show ((([(2, 1), (218809, 1), (451166473145920289829023, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_218809, prime_oneHundredSixtySevenFI_451166473145920289829023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387215 : Nat.totient 197438569645171345394397387215 = 134411747298228231554065711104 := by
  rw [← show ((([(5, 1), (7, 1), (139, 1), (211643, 1), (2162813, 1), (88659702814849, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_7, prime_oneHundredSixtySevenFI_139, prime_oneHundredSixtySevenFI_211643, prime_oneHundredSixtySevenFI_2162813, prime_oneHundredSixtySevenFI_88659702814849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387216 : Nat.totient 197438569645171345394397387216 = 65812856548390448464799129056 := by
  rw [← show ((([(2, 4), (3, 1), (4113303534274403029049945567, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_4113303534274403029049945567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387217 : Nat.totient 197438569645171345394397387217 = 197073618499733595725026270800 := by
  rw [← show ((([(541, 1), (2979727728847, 1), (122478017651371, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_541, prime_oneHundredSixtySevenFI_2979727728847, prime_oneHundredSixtySevenFI_122478017651371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387218 : Nat.totient 197438569645171345394397387218 = 90850088422462318239551659200 := by
  rw [← show ((([(2, 1), (13, 1), (331, 1), (893723, 1), (25670109408545182661, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_13, prime_oneHundredSixtySevenFI_331, prime_oneHundredSixtySevenFI_893723, prime_oneHundredSixtySevenFI_25670109408545182661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387219 : Nat.totient 197438569645171345394397387219 = 131625579682380939925136671872 := by
  rw [← show ((([(3, 2), (986593, 1), (22235733326167409277787, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_986593, prime_oneHundredSixtySevenFI_22235733326167409277787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387220 : Nat.totient 197438569645171345394397387220 = 78965881613810899976103682560 := by
  rw [← show ((([(2, 2), (5, 1), (8311, 1), (3187733, 1), (4166303, 1), (89436733349, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_8311, prime_oneHundredSixtySevenFI_3187733, prime_oneHundredSixtySevenFI_4166303, prime_oneHundredSixtySevenFI_89436733349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387221 : Nat.totient 197438569645171345394397387221 = 197234393254638593227495217292 := by
  rw [← show ((([(967, 1), (204176390532752166902168963, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_967, prime_oneHundredSixtySevenFI_204176390532752166902168963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387222 : Nat.totient 197438569645171345394397387222 = 56411019898620384398399253480 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (4700918324885032033199937791, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_7, prime_oneHundredSixtySevenFI_4700918324885032033199937791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387223 : Nat.totient 197438569645171345394397387223 = 179370803202484679542750742400 := by
  rw [← show ((([(11, 1), (1543, 1), (72461, 1), (35637227, 1), (4504692580733, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_11, prime_oneHundredSixtySevenFI_1543, prime_oneHundredSixtySevenFI_72461, prime_oneHundredSixtySevenFI_35637227, prime_oneHundredSixtySevenFI_4504692580733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387224 : Nat.totient 197438569645171345394397387224 = 97980372719246356864100259840 := by
  rw [← show ((([(2, 3), (233, 1), (313, 1), (83003, 1), (351654091, 1), (11593973059, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_233, prime_oneHundredSixtySevenFI_313, prime_oneHundredSixtySevenFI_83003, prime_oneHundredSixtySevenFI_351654091, prime_oneHundredSixtySevenFI_11593973059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387225 : Nat.totient 197438569645171345394397387225 = 98692656510260268748316344320 := by
  rw [← show ((([(3, 1), (5, 2), (19, 1), (97, 1), (7057, 1), (7547, 1), (10303, 1), (144037, 1), (18072289, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_19, prime_oneHundredSixtySevenFI_97, prime_oneHundredSixtySevenFI_7057, prime_oneHundredSixtySevenFI_7547, prime_oneHundredSixtySevenFI_10303, prime_oneHundredSixtySevenFI_144037, prime_oneHundredSixtySevenFI_18072289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387226 : Nat.totient 197438569645171345394397387226 = 98719284819600966718641939648 := by
  rw [← show ((([(2, 1), (33075045457, 1), (2984705945481708509, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_33075045457, prime_oneHundredSixtySevenFI_2984705945481708509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387227 : Nat.totient 197438569645171345394397387227 = 197438545213100500145363224656 := by
  rw [← show ((([(8081123, 1), (24432070845249026081449, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_8081123, prime_oneHundredSixtySevenFI_24432070845249026081449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387228 : Nat.totient 197438569645171345394397387228 = 59248402818486169511097008640 := by
  rw [← show ((([(2, 2), (3, 2), (17, 1), (23, 1), (7708339363, 1), (1819666968074531, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_17, prime_oneHundredSixtySevenFI_23, prime_oneHundredSixtySevenFI_7708339363, prime_oneHundredSixtySevenFI_1819666968074531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387229 : Nat.totient 197438569645171345394397387229 = 169034783372303300457984000000 := by
  rw [← show ((([(7, 1), (1409, 1), (2833, 1), (9151, 1), (772160947424672501, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_7, prime_oneHundredSixtySevenFI_1409, prime_oneHundredSixtySevenFI_2833, prime_oneHundredSixtySevenFI_9151, prime_oneHundredSixtySevenFI_772160947424672501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387230 : Nat.totient 197438569645171345394397387230 = 78882715006284834652113340416 := by
  rw [← show ((([(2, 1), (5, 1), (853, 1), (622129, 1), (140670643, 1), (264483781853, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_853, prime_oneHundredSixtySevenFI_622129, prime_oneHundredSixtySevenFI_140670643, prime_oneHundredSixtySevenFI_264483781853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387231 : Nat.totient 197438569645171345394397387231 = 116419924597671545167144700928 := by
  rw [← show ((([(3, 1), (13, 1), (37, 1), (67, 1), (3583, 1), (569959575229501383097, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_13, prime_oneHundredSixtySevenFI_37, prime_oneHundredSixtySevenFI_67, prime_oneHundredSixtySevenFI_3583, prime_oneHundredSixtySevenFI_569959575229501383097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387232 : Nat.totient 197438569645171345394397387232 = 94461367137233119217326725120 := by
  rw [← show ((([(2, 5), (31, 1), (89, 1), (2236301305332223466319289, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_31, prime_oneHundredSixtySevenFI_89, prime_oneHundredSixtySevenFI_2236301305332223466319289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387233 : Nat.totient 197438569645171345394397387233 = 196132117003209163656139493376 := by
  rw [← show ((([(157, 1), (4049, 1), (564653, 1), (2361133, 1), (232960599869, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_157, prime_oneHundredSixtySevenFI_4049, prime_oneHundredSixtySevenFI_564653, prime_oneHundredSixtySevenFI_2361133, prime_oneHundredSixtySevenFI_232960599869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387234 : Nat.totient 197438569645171345394397387234 = 55047177919446346544951308800 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (29, 1), (41, 1), (43, 1), (58511030951792460188087, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_11, prime_oneHundredSixtySevenFI_29, prime_oneHundredSixtySevenFI_41, prime_oneHundredSixtySevenFI_43, prime_oneHundredSixtySevenFI_58511030951792460188087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387235 : Nat.totient 197438569645171345394397387235 = 157950844342950037391502137184 := by
  rw [← show ((([(5, 1), (13888003, 1), (2843296759730990055149, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_13888003, prime_oneHundredSixtySevenFI_2843296759730990055149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387236 : Nat.totient 197438569645171345394397387236 = 83206415718496842608525875200 := by
  rw [← show ((([(2, 2), (7, 1), (113, 1), (127, 1), (101051, 1), (865069, 1), (5620829806223, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_7, prime_oneHundredSixtySevenFI_113, prime_oneHundredSixtySevenFI_127, prime_oneHundredSixtySevenFI_101051, prime_oneHundredSixtySevenFI_865069, prime_oneHundredSixtySevenFI_5620829806223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387237 : Nat.totient 197438569645171345394397387237 = 130035855826397368634099362560 := by
  rw [← show ((([(3, 4), (83, 1), (32467, 1), (12872462117, 1), (70269214921, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_83, prime_oneHundredSixtySevenFI_32467, prime_oneHundredSixtySevenFI_12872462117, prime_oneHundredSixtySevenFI_70269214921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387238 : Nat.totient 197438569645171345394397387238 = 98148653114085089675068422240 := by
  rw [← show ((([(2, 1), (173, 1), (22699715923, 1), (25138275126985861, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_173, prime_oneHundredSixtySevenFI_22699715923, prime_oneHundredSixtySevenFI_25138275126985861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387239 : Nat.totient 197438569645171345394397387239 = 197438560194364436823664200120 := by
  rw [← show ((([(21190123, 1), (1481221003, 1), (6290405711231, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_21190123, prime_oneHundredSixtySevenFI_1481221003, prime_oneHundredSixtySevenFI_6290405711231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387240 : Nat.totient 197438569645171345394397387240 = 52650281920625098369192544256 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (15939433, 1), (4097030813, 1), (25194668663, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_15939433, prime_oneHundredSixtySevenFI_4097030813, prime_oneHundredSixtySevenFI_25194668663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387241 : Nat.totient 197438569645171345394397387241 = 193713313613621916882257463792 := by
  rw [← show ((([(53, 1), (380995484899, 1), (9777690756698903, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_53, prime_oneHundredSixtySevenFI_380995484899, prime_oneHundredSixtySevenFI_9777690756698903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387242 : Nat.totient 197438569645171345394397387242 = 98555026445112350759973907200 := by
  rw [← show ((([(2, 1), (601, 1), (1545568713257, 1), (106276981411253, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_601, prime_oneHundredSixtySevenFI_1545568713257, prime_oneHundredSixtySevenFI_106276981411253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387243 : Nat.totient 197438569645171345394397387243 = 112820410336256416974384041760 := by
  rw [← show ((([(3, 1), (7, 1), (69239, 1), (37713613027, 1), (3600507948211, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_7, prime_oneHundredSixtySevenFI_69239, prime_oneHundredSixtySevenFI_37713613027, prime_oneHundredSixtySevenFI_3600507948211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387244 : Nat.totient 197438569645171345394397387244 = 86329220668449024982587383808 := by
  rw [← show ((([(2, 2), (13, 1), (19, 1), (790523, 1), (1175969, 1), (14193043, 1), (15145693, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_13, prime_oneHundredSixtySevenFI_19, prime_oneHundredSixtySevenFI_790523, prime_oneHundredSixtySevenFI_1175969, prime_oneHundredSixtySevenFI_14193043, prime_oneHundredSixtySevenFI_15145693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387245 : Nat.totient 197438569645171345394397387245 = 135093554763384273252005376000 := by
  rw [← show ((([(5, 1), (11, 1), (17, 1), (2621, 1), (110198386171, 1), (731102265797, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_11, prime_oneHundredSixtySevenFI_17, prime_oneHundredSixtySevenFI_2621, prime_oneHundredSixtySevenFI_110198386171, prime_oneHundredSixtySevenFI_731102265797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387246 : Nat.totient 197438569645171345394397387246 = 64730883327606797005364837760 := by
  rw [← show ((([(2, 1), (3, 2), (61, 1), (21059, 1), (8538703069776437168953, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_61, prime_oneHundredSixtySevenFI_21059, prime_oneHundredSixtySevenFI_8538703069776437168953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387247 : Nat.totient 197438569645171345394397387247 = 193405951360505577923867880000 := by
  rw [← show ((([(59, 1), (283, 1), (531551, 1), (22245829761113316601, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_59, prime_oneHundredSixtySevenFI_283, prime_oneHundredSixtySevenFI_531551, prime_oneHundredSixtySevenFI_22245829761113316601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387248 : Nat.totient 197438569645171345394397387248 = 97608806524667444637595684032 := by
  rw [← show ((([(2, 4), (103, 1), (643, 1), (186321862066816788523907, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_103, prime_oneHundredSixtySevenFI_643, prime_oneHundredSixtySevenFI_186321862066816788523907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387249 : Nat.totient 197438569645171345394397387249 = 131625713096780896929598258164 := by
  rw [← show ((([(3, 1), (65812856548390448464799129083, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_65812856548390448464799129083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387250 : Nat.totient 197438569645171345394397387250 = 67672828209806243603681896800 := by
  rw [← show ((([(2, 1), (5, 3), (7, 2), (3319, 1), (4856111556718493900779, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_7, prime_oneHundredSixtySevenFI_3319, prime_oneHundredSixtySevenFI_4856111556718493900779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387251 : Nat.totient 197438569645171345394397387251 = 183495549803424157922802702336 := by
  rw [← show ((([(23, 1), (73, 1), (107, 1), (179, 1), (7351635589, 1), (835142374057, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_23, prime_oneHundredSixtySevenFI_73, prime_oneHundredSixtySevenFI_107, prime_oneHundredSixtySevenFI_179, prime_oneHundredSixtySevenFI_7351635589, prime_oneHundredSixtySevenFI_835142374057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387252 : Nat.totient 197438569645171345394397387252 = 65812856548126527667929331776 := by
  rw [← show ((([(2, 2), (3, 1), (249366878489, 1), (65979949850570839, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_249366878489, prime_oneHundredSixtySevenFI_65979949850570839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387253 : Nat.totient 197438569645171345394397387253 = 193190629667990918899080250800 := by
  rw [← show ((([(47, 1), (4111, 1), (1690219, 1), (604565947988332511, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_47, prime_oneHundredSixtySevenFI_4111, prime_oneHundredSixtySevenFI_1690219, prime_oneHundredSixtySevenFI_604565947988332511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387254 : Nat.totient 197438569645171345394397387254 = 97285040970666487759943270400 := by
  rw [← show ((([(2, 1), (71, 1), (2309, 1), (57977, 1), (69107681, 1), (150292621489, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_71, prime_oneHundredSixtySevenFI_2309, prime_oneHundredSixtySevenFI_57977, prime_oneHundredSixtySevenFI_69107681, prime_oneHundredSixtySevenFI_150292621489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387255 : Nat.totient 197438569645171345394397387255 = 105144106033921857636481445376 := by
  rw [← show ((([(3, 2), (5, 1), (673, 1), (6519351812619162799881043, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_673, prime_oneHundredSixtySevenFI_6519351812619162799881043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387256 : Nat.totient 197438569645171345394397387256 = 88587072487931439122528256000 := by
  rw [← show ((([(2, 3), (11, 1), (79, 1), (5281, 1), (17923, 1), (300051194740345681, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_11, prime_oneHundredSixtySevenFI_79, prime_oneHundredSixtySevenFI_5281, prime_oneHundredSixtySevenFI_17923, prime_oneHundredSixtySevenFI_300051194740345681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387257 : Nat.totient 197438569645171345394397387257 = 156213931252990992258971225088 := by
  rw [← show ((([(7, 1), (13, 1), (135029, 1), (7122149, 1), (7287733, 1), (309570839, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_7, prime_oneHundredSixtySevenFI_13, prime_oneHundredSixtySevenFI_135029, prime_oneHundredSixtySevenFI_7122149, prime_oneHundredSixtySevenFI_7287733, prime_oneHundredSixtySevenFI_309570839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387258 : Nat.totient 197438569645171345394397387258 = 65812856543812949327760670656 := by
  rw [← show ((([(2, 1), (3, 1), (14377470097, 1), (2288749554141759119, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_14377470097, prime_oneHundredSixtySevenFI_2288749554141759119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387259 : Nat.totient 197438569645171345394397387259 = 196605696407381818449351228000 := by
  rw [← show ((([(439, 1), (661, 1), (2311, 1), (294419161081523020111, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_439, prime_oneHundredSixtySevenFI_661, prime_oneHundredSixtySevenFI_2311, prime_oneHundredSixtySevenFI_294419161081523020111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387260 : Nat.totient 197438569645171345394397387260 = 78975427858068538157758954896 := by
  rw [← show ((([(2, 2), (5, 1), (9871928482258567269719869363, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_9871928482258567269719869363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387261 : Nat.totient 197438569645171345394397387261 = 131624571710826964585138602240 := by
  rw [← show ((([(3, 1), (115321, 1), (315548325769, 1), (1808574742463, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_115321, prime_oneHundredSixtySevenFI_315548325769, prime_oneHundredSixtySevenFI_1808574742463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387262 : Nat.totient 197438569645171345394397387262 = 92185896033925073166751444480 := by
  rw [← show ((([(2, 1), (17, 1), (131, 1), (5387, 1), (41106077, 1), (200183729666747, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_17, prime_oneHundredSixtySevenFI_131, prime_oneHundredSixtySevenFI_5387, prime_oneHundredSixtySevenFI_41106077, prime_oneHundredSixtySevenFI_200183729666747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387263 : Nat.totient 197438569645171345394397387263 = 172411851481561556139480791040 := by
  rw [← show ((([(19, 1), (29, 1), (31, 1), (109, 1), (229, 1), (382044709, 1), (1212111394027, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_19, prime_oneHundredSixtySevenFI_29, prime_oneHundredSixtySevenFI_31, prime_oneHundredSixtySevenFI_109, prime_oneHundredSixtySevenFI_229, prime_oneHundredSixtySevenFI_382044709, prime_oneHundredSixtySevenFI_1212111394027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387264 : Nat.totient 197438569645171345394397387264 = 56411019822603430640490577920 := by
  rw [← show ((([(2, 9), (3, 3), (7, 1), (742084921, 1), (2749455050663513, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_7, prime_oneHundredSixtySevenFI_742084921, prime_oneHundredSixtySevenFI_2749455050663513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387265 : Nat.totient 197438569645171345394397387265 = 157202273461558227612600762480 := by
  rw [← show ((([(5, 1), (211, 1), (187145563644712175729286623, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_211, prime_oneHundredSixtySevenFI_187145563644712175729286623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387266 : Nat.totient 197438569645171345394397387266 = 98719284822572883488060380608 := by
  rw [← show ((([(2, 1), (7723615901257, 1), (12781485522411769, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_7723615901257, prime_oneHundredSixtySevenFI_12781485522411769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387267 : Nat.totient 197438569645171345394397387267 = 119629391770485168989443963200 := by
  rw [← show ((([(3, 1), (11, 2), (3943, 1), (5118777541, 1), (26948359863043, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_11, prime_oneHundredSixtySevenFI_3943, prime_oneHundredSixtySevenFI_5118777541, prime_oneHundredSixtySevenFI_26948359863043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387268 : Nat.totient 197438569645171345394397387268 = 95422847029473038168462450688 := by
  rw [← show ((([(2, 2), (37, 1), (193, 1), (1237, 1), (1787, 1), (3126934034869599323, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_37, prime_oneHundredSixtySevenFI_193, prime_oneHundredSixtySevenFI_1237, prime_oneHundredSixtySevenFI_1787, prime_oneHundredSixtySevenFI_3126934034869599323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387269 : Nat.totient 197438569645171345394397387269 = 197438569645171345394397387268 := by
  rw [← show ((([(197438569645171345394397387269, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_197438569645171345394397387269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387270 : Nat.totient 197438569645171345394397387270 = 48557072835442757601736261632 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (13, 1), (1129, 1), (361217, 1), (5482039, 1), (226445213359, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_13, prime_oneHundredSixtySevenFI_1129, prime_oneHundredSixtySevenFI_361217, prime_oneHundredSixtySevenFI_5482039, prime_oneHundredSixtySevenFI_226445213359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387271 : Nat.totient 197438569645171345394397387271 = 168112109272056952577799621600 := by
  rw [← show ((([(7, 1), (151, 1), (1096427, 1), (3476503, 1), (49004355142163, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_7, prime_oneHundredSixtySevenFI_151, prime_oneHundredSixtySevenFI_1096427, prime_oneHundredSixtySevenFI_3476503, prime_oneHundredSixtySevenFI_49004355142163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387272 : Nat.totient 197438569645171345394397387272 = 98711743854703900890113053824 := by
  rw [← show ((([(2, 3), (13103, 1), (14368567, 1), (131086452514152809, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_13103, prime_oneHundredSixtySevenFI_14368567, prime_oneHundredSixtySevenFI_131086452514152809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387273 : Nat.totient 197438569645171345394397387273 = 131625584571722954521787858880 := by
  rw [← show ((([(3, 2), (1712531, 1), (2547689, 1), (5028108410867683, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_1712531, prime_oneHundredSixtySevenFI_2547689, prime_oneHundredSixtySevenFI_5028108410867683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387274 : Nat.totient 197438569645171345394397387274 = 94426437465544747052930668800 := by
  rw [← show ((([(2, 1), (23, 1), (139901, 1), (3192047, 1), (9611342825104177, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_23, prime_oneHundredSixtySevenFI_139901, prime_oneHundredSixtySevenFI_3192047, prime_oneHundredSixtySevenFI_9611342825104177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387275 : Nat.totient 197438569645171345394397387275 = 154098395820621537868797960000 := by
  rw [← show ((([(5, 2), (41, 1), (192622994775776922335997451, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_41, prime_oneHundredSixtySevenFI_192622994775776922335997451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387276 : Nat.totient 197438569645171345394397387276 = 65812856548390448464799129088 := by
  rw [← show ((([(2, 2), (3, 1), (16453214137097612116199782273, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_16453214137097612116199782273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387277 : Nat.totient 197438569645171345394397387277 = 192846975002260383873597447996 := by
  rw [← show ((([(43, 1), (4591594642910961520799939239, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_43, prime_oneHundredSixtySevenFI_4591594642910961520799939239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387278 : Nat.totient 197438569645171345394397387278 = 76441650025335301352110187520 := by
  rw [← show ((([(2, 1), (7, 1), (11, 1), (163, 1), (7253, 1), (525185989, 1), (2064870701017, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_7, prime_oneHundredSixtySevenFI_11, prime_oneHundredSixtySevenFI_163, prime_oneHundredSixtySevenFI_7253, prime_oneHundredSixtySevenFI_525185989, prime_oneHundredSixtySevenFI_2064870701017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387279 : Nat.totient 197438569645171345394397387279 = 123326178127002180684456689664 := by
  rw [← show ((([(3, 1), (17, 1), (239, 1), (4457, 1), (13033, 1), (90373, 1), (3085589801647, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_17, prime_oneHundredSixtySevenFI_239, prime_oneHundredSixtySevenFI_4457, prime_oneHundredSixtySevenFI_13033, prime_oneHundredSixtySevenFI_90373, prime_oneHundredSixtySevenFI_3085589801647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387280 : Nat.totient 197438569645171345394397387280 = 78975427858068538157758954880 := by
  rw [← show ((([(2, 4), (5, 1), (2467982120564641817429967341, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_2467982120564641817429967341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387281 : Nat.totient 197438569645171345394397387281 = 197438541562267343114722291200 := by
  rw [← show ((([(7030561, 1), (28082904002279668065521, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_7030561, prime_oneHundredSixtySevenFI_28082904002279668065521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387282 : Nat.totient 197438569645171345394397387282 = 62299183139776496252498987520 := by
  rw [← show ((([(2, 1), (3, 2), (19, 1), (1373, 1), (14071, 1), (244373293, 1), (122280343109, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_19, prime_oneHundredSixtySevenFI_1373, prime_oneHundredSixtySevenFI_14071, prime_oneHundredSixtySevenFI_244373293, prime_oneHundredSixtySevenFI_122280343109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387283 : Nat.totient 197438569645171345394397387283 = 182243063634498692694699747840 := by
  rw [← show ((([(13, 1), (27259, 1), (147229, 1), (3784298292927673681, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_13, prime_oneHundredSixtySevenFI_27259, prime_oneHundredSixtySevenFI_147229, prime_oneHundredSixtySevenFI_3784298292927673681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387284 : Nat.totient 197438569645171345394397387284 = 98719232175931401812041231680 := by
  rw [← show ((([(2, 2), (1886471, 1), (311892697, 1), (83891250011083, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_1886471, prime_oneHundredSixtySevenFI_311892697, prime_oneHundredSixtySevenFI_83891250011083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387285 : Nat.totient 197438569645171345394397387285 = 90257631781555923848369241408 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (1604959859, 1), (1171597731500656063, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_7, prime_oneHundredSixtySevenFI_1604959859, prime_oneHundredSixtySevenFI_1171597731500656063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387286 : Nat.totient 197438569645171345394397387286 = 98407867520306222625598697448 := by
  rw [← show ((([(2, 1), (317, 1), (311417302279450071599995879, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_317, prime_oneHundredSixtySevenFI_311417302279450071599995879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387287 : Nat.totient 197438569645171345394397387287 = 197438569640347488428473428840 := by
  rw [← show ((([(40929607307, 1), (4823856924994351141, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_40929607307, prime_oneHundredSixtySevenFI_4823856924994351141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387288 : Nat.totient 197438569645171345394397387288 = 65723053882795035257439014400 := by
  rw [← show ((([(2, 3), (3, 1), (733, 1), (3915941, 1), (252480271, 1), (11351498399, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_733, prime_oneHundredSixtySevenFI_3915941, prime_oneHundredSixtySevenFI_252480271, prime_oneHundredSixtySevenFI_11351498399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387289 : Nat.totient 197438569645171345394397387289 = 179189960005786104941341074000 := by
  rw [← show ((([(11, 1), (599, 1), (29964876255148178083836301, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_11, prime_oneHundredSixtySevenFI_599, prime_oneHundredSixtySevenFI_29964876255148178083836301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387290 : Nat.totient 197438569645171345394397387290 = 78973588359863296807670968000 := by
  rw [← show ((([(2, 1), (5, 1), (79103, 1), (93893, 1), (2658311230442094251, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_79103, prime_oneHundredSixtySevenFI_93893, prime_oneHundredSixtySevenFI_2658311230442094251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387291 : Nat.totient 197438569645171345394397387291 = 131622103795561348008724026624 := by
  rw [← show ((([(3, 3), (36469, 1), (2535700073, 1), (79076327956309, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_36469, prime_oneHundredSixtySevenFI_2535700073, prime_oneHundredSixtySevenFI_79076327956309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387292 : Nat.totient 197438569645171345394397387292 = 81698680706701762267745126400 := by
  rw [← show ((([(2, 2), (7, 1), (29, 1), (2163221, 1), (112402268579530693921, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_7, prime_oneHundredSixtySevenFI_29, prime_oneHundredSixtySevenFI_2163221, prime_oneHundredSixtySevenFI_112402268579530693921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387293 : Nat.totient 197438569645171345394397387293 = 196687690598025354009599093760 := by
  rw [← show ((([(263, 1), (1699793, 1), (4244497, 1), (104052850052891, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_263, prime_oneHundredSixtySevenFI_1699793, prime_oneHundredSixtySevenFI_4244497, prime_oneHundredSixtySevenFI_104052850052891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387294 : Nat.totient 197438569645171345394397387294 = 62487895520127805315814578560 := by
  rw [← show ((([(2, 1), (3, 1), (31, 1), (53, 1), (231299, 1), (86590336453694386757, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_31, prime_oneHundredSixtySevenFI_53, prime_oneHundredSixtySevenFI_231299, prime_oneHundredSixtySevenFI_86590336453694386757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387295 : Nat.totient 197438569645171345394397387295 = 157949299273962720613711749120 := by
  rw [← show ((([(5, 1), (101483, 1), (10242004921, 1), (37991261488513, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_101483, prime_oneHundredSixtySevenFI_10242004921, prime_oneHundredSixtySevenFI_37991261488513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387296 : Nat.totient 197438569645171345394397387296 = 85765170135006116891161952256 := by
  rw [← show ((([(2, 5), (13, 1), (17, 1), (220140317, 1), (126820703088853129, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_13, prime_oneHundredSixtySevenFI_17, prime_oneHundredSixtySevenFI_220140317, prime_oneHundredSixtySevenFI_126820703088853129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387297 : Nat.totient 197438569645171345394397387297 = 125902855982936861387164488960 := by
  rw [← show ((([(3, 1), (23, 1), (5551358353, 1), (515446556253363421, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_23, prime_oneHundredSixtySevenFI_5551358353, prime_oneHundredSixtySevenFI_515446556253363421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387298 : Nat.totient 197438569645171345394397387298 = 96682589118254856163696939008 := by
  rw [← show ((([(2, 1), (67, 1), (199, 1), (1297, 1), (940426477, 1), (6070288014737, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_67, prime_oneHundredSixtySevenFI_199, prime_oneHundredSixtySevenFI_1297, prime_oneHundredSixtySevenFI_940426477, prime_oneHundredSixtySevenFI_6070288014737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387299 : Nat.totient 197438569645171345394397387299 = 169230991261920824643020629344 := by
  rw [← show ((([(7, 2), (81817, 1), (49248427150679813659403, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_7, prime_oneHundredSixtySevenFI_81817, prime_oneHundredSixtySevenFI_49248427150679813659403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387300 : Nat.totient 197438569645171345394397387300 = 46287234190009931786640000000 := by
  rw [← show ((([(2, 2), (3, 2), (5, 2), (11, 1), (47, 1), (101, 1), (491, 1), (8556498482329549651, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_2, prime_oneHundredSixtySevenFI_3, prime_oneHundredSixtySevenFI_5, prime_oneHundredSixtySevenFI_11, prime_oneHundredSixtySevenFI_47, prime_oneHundredSixtySevenFI_101, prime_oneHundredSixtySevenFI_491, prime_oneHundredSixtySevenFI_8556498482329549651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySevenFI_197438569645171345394397387301 : Nat.totient 197438569645171345394397387301 = 187028544634356316801909578480 := by
  rw [← show ((([(19, 1), (10099, 1), (1028963626649701353413821, 1)] : List FactorBlock).map factorBlockValue).prod) = 197438569645171345394397387301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySevenFI_19, prime_oneHundredSixtySevenFI_10099, prime_oneHundredSixtySevenFI_1028963626649701353413821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredSixtySevenFI : certifiedKill 1 197438569645171345394397387199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredSixtySevenFI_197438569645171345394397387200, phi_oneHundredSixtySevenFI_197438569645171345394397387201, phi_oneHundredSixtySevenFI_197438569645171345394397387202,
    phi_oneHundredSixtySevenFI_197438569645171345394397387203, phi_oneHundredSixtySevenFI_197438569645171345394397387204, phi_oneHundredSixtySevenFI_197438569645171345394397387205,
    phi_oneHundredSixtySevenFI_197438569645171345394397387206, phi_oneHundredSixtySevenFI_197438569645171345394397387207, phi_oneHundredSixtySevenFI_197438569645171345394397387208,
    phi_oneHundredSixtySevenFI_197438569645171345394397387209, phi_oneHundredSixtySevenFI_197438569645171345394397387210, phi_oneHundredSixtySevenFI_197438569645171345394397387211,
    phi_oneHundredSixtySevenFI_197438569645171345394397387212, phi_oneHundredSixtySevenFI_197438569645171345394397387213, phi_oneHundredSixtySevenFI_197438569645171345394397387214,
    phi_oneHundredSixtySevenFI_197438569645171345394397387215, phi_oneHundredSixtySevenFI_197438569645171345394397387216, phi_oneHundredSixtySevenFI_197438569645171345394397387217,
    phi_oneHundredSixtySevenFI_197438569645171345394397387218, phi_oneHundredSixtySevenFI_197438569645171345394397387219, phi_oneHundredSixtySevenFI_197438569645171345394397387220,
    phi_oneHundredSixtySevenFI_197438569645171345394397387221, phi_oneHundredSixtySevenFI_197438569645171345394397387222, phi_oneHundredSixtySevenFI_197438569645171345394397387223,
    phi_oneHundredSixtySevenFI_197438569645171345394397387224, phi_oneHundredSixtySevenFI_197438569645171345394397387225, phi_oneHundredSixtySevenFI_197438569645171345394397387226,
    phi_oneHundredSixtySevenFI_197438569645171345394397387227, phi_oneHundredSixtySevenFI_197438569645171345394397387228, phi_oneHundredSixtySevenFI_197438569645171345394397387229,
    phi_oneHundredSixtySevenFI_197438569645171345394397387230, phi_oneHundredSixtySevenFI_197438569645171345394397387231, phi_oneHundredSixtySevenFI_197438569645171345394397387232,
    phi_oneHundredSixtySevenFI_197438569645171345394397387233, phi_oneHundredSixtySevenFI_197438569645171345394397387234, phi_oneHundredSixtySevenFI_197438569645171345394397387235,
    phi_oneHundredSixtySevenFI_197438569645171345394397387236, phi_oneHundredSixtySevenFI_197438569645171345394397387237, phi_oneHundredSixtySevenFI_197438569645171345394397387238,
    phi_oneHundredSixtySevenFI_197438569645171345394397387239, phi_oneHundredSixtySevenFI_197438569645171345394397387240, phi_oneHundredSixtySevenFI_197438569645171345394397387241,
    phi_oneHundredSixtySevenFI_197438569645171345394397387242, phi_oneHundredSixtySevenFI_197438569645171345394397387243, phi_oneHundredSixtySevenFI_197438569645171345394397387244,
    phi_oneHundredSixtySevenFI_197438569645171345394397387245, phi_oneHundredSixtySevenFI_197438569645171345394397387246, phi_oneHundredSixtySevenFI_197438569645171345394397387247,
    phi_oneHundredSixtySevenFI_197438569645171345394397387248, phi_oneHundredSixtySevenFI_197438569645171345394397387249, phi_oneHundredSixtySevenFI_197438569645171345394397387250,
    phi_oneHundredSixtySevenFI_197438569645171345394397387251, phi_oneHundredSixtySevenFI_197438569645171345394397387252, phi_oneHundredSixtySevenFI_197438569645171345394397387253,
    phi_oneHundredSixtySevenFI_197438569645171345394397387254, phi_oneHundredSixtySevenFI_197438569645171345394397387255, phi_oneHundredSixtySevenFI_197438569645171345394397387256,
    phi_oneHundredSixtySevenFI_197438569645171345394397387257, phi_oneHundredSixtySevenFI_197438569645171345394397387258, phi_oneHundredSixtySevenFI_197438569645171345394397387259,
    phi_oneHundredSixtySevenFI_197438569645171345394397387260, phi_oneHundredSixtySevenFI_197438569645171345394397387261, phi_oneHundredSixtySevenFI_197438569645171345394397387262,
    phi_oneHundredSixtySevenFI_197438569645171345394397387263, phi_oneHundredSixtySevenFI_197438569645171345394397387264, phi_oneHundredSixtySevenFI_197438569645171345394397387265,
    phi_oneHundredSixtySevenFI_197438569645171345394397387266, phi_oneHundredSixtySevenFI_197438569645171345394397387267, phi_oneHundredSixtySevenFI_197438569645171345394397387268,
    phi_oneHundredSixtySevenFI_197438569645171345394397387269, phi_oneHundredSixtySevenFI_197438569645171345394397387270, phi_oneHundredSixtySevenFI_197438569645171345394397387271,
    phi_oneHundredSixtySevenFI_197438569645171345394397387272, phi_oneHundredSixtySevenFI_197438569645171345394397387273, phi_oneHundredSixtySevenFI_197438569645171345394397387274,
    phi_oneHundredSixtySevenFI_197438569645171345394397387275, phi_oneHundredSixtySevenFI_197438569645171345394397387276, phi_oneHundredSixtySevenFI_197438569645171345394397387277,
    phi_oneHundredSixtySevenFI_197438569645171345394397387278, phi_oneHundredSixtySevenFI_197438569645171345394397387279, phi_oneHundredSixtySevenFI_197438569645171345394397387280,
    phi_oneHundredSixtySevenFI_197438569645171345394397387281, phi_oneHundredSixtySevenFI_197438569645171345394397387282, phi_oneHundredSixtySevenFI_197438569645171345394397387283,
    phi_oneHundredSixtySevenFI_197438569645171345394397387284, phi_oneHundredSixtySevenFI_197438569645171345394397387285, phi_oneHundredSixtySevenFI_197438569645171345394397387286,
    phi_oneHundredSixtySevenFI_197438569645171345394397387287, phi_oneHundredSixtySevenFI_197438569645171345394397387288, phi_oneHundredSixtySevenFI_197438569645171345394397387289,
    phi_oneHundredSixtySevenFI_197438569645171345394397387290, phi_oneHundredSixtySevenFI_197438569645171345394397387291, phi_oneHundredSixtySevenFI_197438569645171345394397387292,
    phi_oneHundredSixtySevenFI_197438569645171345394397387293, phi_oneHundredSixtySevenFI_197438569645171345394397387294, phi_oneHundredSixtySevenFI_197438569645171345394397387295,
    phi_oneHundredSixtySevenFI_197438569645171345394397387296, phi_oneHundredSixtySevenFI_197438569645171345394397387297, phi_oneHundredSixtySevenFI_197438569645171345394397387298,
    phi_oneHundredSixtySevenFI_197438569645171345394397387299, phi_oneHundredSixtySevenFI_197438569645171345394397387300, phi_oneHundredSixtySevenFI_197438569645171345394397387301]

end TotientTailPeriodKiller
end Erdos249257
