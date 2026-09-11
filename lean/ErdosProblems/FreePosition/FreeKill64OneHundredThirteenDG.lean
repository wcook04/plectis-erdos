import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredThirteenDGFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredThirteenDGFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredThirteenDGFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredThirteenDGFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredThirteenDGFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredThirteenDGFastPow a n * oneHundredThirteenDGFastPow a n * a else oneHundredThirteenDGFastPow a n * oneHundredThirteenDGFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredThirteenDG_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredThirteenDG_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredThirteenDG_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredThirteenDG_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredThirteenDG_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredThirteenDG_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredThirteenDG_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredThirteenDG_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredThirteenDG_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredThirteenDG_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredThirteenDG_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredThirteenDG_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredThirteenDG_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredThirteenDG_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredThirteenDG_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredThirteenDG_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredThirteenDG_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredThirteenDG_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredThirteenDG_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredThirteenDG_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredThirteenDG_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredThirteenDG_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredThirteenDG_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredThirteenDG_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredThirteenDG_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredThirteenDG_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredThirteenDG_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredThirteenDG_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredThirteenDG_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredThirteenDG_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredThirteenDG_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredThirteenDG_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredThirteenDG_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredThirteenDG_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredThirteenDG_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredThirteenDG_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredThirteenDG_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredThirteenDG_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredThirteenDG_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredThirteenDG_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredThirteenDG_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredThirteenDG_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredThirteenDG_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredThirteenDG_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredThirteenDG_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredThirteenDG_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredThirteenDG_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredThirteenDG_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredThirteenDG_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredThirteenDG_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredThirteenDG_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredThirteenDG_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredThirteenDG_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredThirteenDG_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredThirteenDG_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredThirteenDG_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredThirteenDG_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredThirteenDG_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredThirteenDG_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredThirteenDG_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredThirteenDG_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredThirteenDG_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredThirteenDG_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredThirteenDG_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredThirteenDG_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredThirteenDG_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredThirteenDG_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredThirteenDG_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredThirteenDG_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredThirteenDG_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredThirteenDG_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredThirteenDG_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredThirteenDG_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredThirteenDG_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredThirteenDG_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredThirteenDG_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredThirteenDG_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredThirteenDG_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredThirteenDG_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredThirteenDG_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredThirteenDG_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredThirteenDG_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredThirteenDG_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredThirteenDG_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredThirteenDG_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredThirteenDG_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredThirteenDG_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredThirteenDG_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredThirteenDG_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredThirteenDG_761 : Nat.Prime 761 := by norm_num

private theorem prime_oneHundredThirteenDG_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredThirteenDG_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredThirteenDG_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredThirteenDG_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredThirteenDG_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredThirteenDG_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredThirteenDG_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredThirteenDG_863 : Nat.Prime 863 := by norm_num

private theorem prime_oneHundredThirteenDG_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredThirteenDG_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredThirteenDG_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredThirteenDG_911 : Nat.Prime 911 := by norm_num

private theorem prime_oneHundredThirteenDG_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredThirteenDG_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredThirteenDG_953 : Nat.Prime 953 := by norm_num

private theorem prime_oneHundredThirteenDG_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredThirteenDG_983 : Nat.Prime 983 := by norm_num

private theorem prime_oneHundredThirteenDG_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredThirteenDG_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_oneHundredThirteenDG_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_oneHundredThirteenDG_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredThirteenDG_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredThirteenDG_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredThirteenDG_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_oneHundredThirteenDG_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_oneHundredThirteenDG_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_oneHundredThirteenDG_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredThirteenDG_1213 : Nat.Prime 1213 := by norm_num

private theorem prime_oneHundredThirteenDG_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_oneHundredThirteenDG_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_oneHundredThirteenDG_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_oneHundredThirteenDG_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredThirteenDG_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_oneHundredThirteenDG_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_oneHundredThirteenDG_1423 : Nat.Prime 1423 := by norm_num

private theorem prime_oneHundredThirteenDG_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_oneHundredThirteenDG_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_oneHundredThirteenDG_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_oneHundredThirteenDG_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_oneHundredThirteenDG_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_oneHundredThirteenDG_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_oneHundredThirteenDG_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredThirteenDG_1607 : Nat.Prime 1607 := by norm_num

private theorem prime_oneHundredThirteenDG_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_oneHundredThirteenDG_1721 : Nat.Prime 1721 := by norm_num

private theorem prime_oneHundredThirteenDG_1747 : Nat.Prime 1747 := by norm_num

private theorem prime_oneHundredThirteenDG_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_oneHundredThirteenDG_1867 : Nat.Prime 1867 := by norm_num

private theorem prime_oneHundredThirteenDG_1879 : Nat.Prime 1879 := by norm_num

private theorem prime_oneHundredThirteenDG_1931 : Nat.Prime 1931 := by norm_num

private theorem prime_oneHundredThirteenDG_1973 : Nat.Prime 1973 := by norm_num

private theorem prime_oneHundredThirteenDG_1979 : Nat.Prime 1979 := by norm_num

private theorem prime_oneHundredThirteenDG_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_oneHundredThirteenDG_2029 : Nat.Prime 2029 := by norm_num

private theorem prime_oneHundredThirteenDG_2053 : Nat.Prime 2053 := by norm_num

private theorem prime_oneHundredThirteenDG_2069 : Nat.Prime 2069 := by norm_num

private theorem prime_oneHundredThirteenDG_2131 : Nat.Prime 2131 := by norm_num

private theorem prime_oneHundredThirteenDG_2287 : Nat.Prime 2287 := by norm_num

private theorem prime_oneHundredThirteenDG_2347 : Nat.Prime 2347 := by norm_num

private theorem prime_oneHundredThirteenDG_2377 : Nat.Prime 2377 := by norm_num

private theorem prime_oneHundredThirteenDG_2399 : Nat.Prime 2399 := by norm_num

private theorem prime_oneHundredThirteenDG_2411 : Nat.Prime 2411 := by norm_num

private theorem prime_oneHundredThirteenDG_2473 : Nat.Prime 2473 := by norm_num

private theorem prime_oneHundredThirteenDG_2617 : Nat.Prime 2617 := by norm_num

private theorem prime_oneHundredThirteenDG_2633 : Nat.Prime 2633 := by norm_num

private theorem prime_oneHundredThirteenDG_2663 : Nat.Prime 2663 := by norm_num

private theorem prime_oneHundredThirteenDG_2713 : Nat.Prime 2713 := by norm_num

private theorem prime_oneHundredThirteenDG_2741 : Nat.Prime 2741 := by norm_num

private theorem prime_oneHundredThirteenDG_2917 : Nat.Prime 2917 := by norm_num

private theorem prime_oneHundredThirteenDG_3019 : Nat.Prime 3019 := by norm_num

private theorem prime_oneHundredThirteenDG_3067 : Nat.Prime 3067 := by norm_num

private theorem prime_oneHundredThirteenDG_3209 : Nat.Prime 3209 := by norm_num

private theorem prime_oneHundredThirteenDG_3257 : Nat.Prime 3257 := by norm_num

private theorem prime_oneHundredThirteenDG_3299 : Nat.Prime 3299 := by norm_num

private theorem prime_oneHundredThirteenDG_3457 : Nat.Prime 3457 := by norm_num

private theorem prime_oneHundredThirteenDG_3607 : Nat.Prime 3607 := by norm_num

private theorem prime_oneHundredThirteenDG_3613 : Nat.Prime 3613 := by norm_num

private theorem prime_oneHundredThirteenDG_3863 : Nat.Prime 3863 := by norm_num

private theorem prime_oneHundredThirteenDG_3907 : Nat.Prime 3907 := by norm_num

private theorem prime_oneHundredThirteenDG_3929 : Nat.Prime 3929 := by norm_num

private theorem prime_oneHundredThirteenDG_4093 : Nat.Prime 4093 := by norm_num

private theorem prime_oneHundredThirteenDG_4127 : Nat.Prime 4127 := by norm_num

private theorem prime_oneHundredThirteenDG_4133 : Nat.Prime 4133 := by norm_num

private theorem prime_oneHundredThirteenDG_4231 : Nat.Prime 4231 := by norm_num

private theorem prime_oneHundredThirteenDG_4519 : Nat.Prime 4519 := by norm_num

private theorem prime_oneHundredThirteenDG_4603 : Nat.Prime 4603 := by norm_num

private theorem prime_oneHundredThirteenDG_4663 : Nat.Prime 4663 := by norm_num

private theorem prime_oneHundredThirteenDG_4931 : Nat.Prime 4931 := by norm_num

private theorem prime_oneHundredThirteenDG_5051 : Nat.Prime 5051 := by norm_num

private theorem prime_oneHundredThirteenDG_5189 : Nat.Prime 5189 := by norm_num

private theorem prime_oneHundredThirteenDG_5209 : Nat.Prime 5209 := by norm_num

private theorem prime_oneHundredThirteenDG_5309 : Nat.Prime 5309 := by norm_num

private theorem prime_oneHundredThirteenDG_5351 : Nat.Prime 5351 := by norm_num

private theorem prime_oneHundredThirteenDG_5399 : Nat.Prime 5399 := by norm_num

private theorem prime_oneHundredThirteenDG_5437 : Nat.Prime 5437 := by norm_num

private theorem prime_oneHundredThirteenDG_5483 : Nat.Prime 5483 := by norm_num

private theorem prime_oneHundredThirteenDG_5501 : Nat.Prime 5501 := by norm_num

private theorem prime_oneHundredThirteenDG_5623 : Nat.Prime 5623 := by norm_num

private theorem prime_oneHundredThirteenDG_5737 : Nat.Prime 5737 := by norm_num

private theorem prime_oneHundredThirteenDG_6101 : Nat.Prime 6101 := by norm_num

private theorem prime_oneHundredThirteenDG_6131 : Nat.Prime 6131 := by norm_num

private theorem prime_oneHundredThirteenDG_6299 : Nat.Prime 6299 := by norm_num

private theorem prime_oneHundredThirteenDG_6361 : Nat.Prime 6361 := by norm_num

private theorem prime_oneHundredThirteenDG_6469 : Nat.Prime 6469 := by norm_num

private theorem prime_oneHundredThirteenDG_6829 : Nat.Prime 6829 := by norm_num

private theorem prime_oneHundredThirteenDG_6833 : Nat.Prime 6833 := by norm_num

private theorem prime_oneHundredThirteenDG_6967 : Nat.Prime 6967 := by norm_num

private theorem prime_oneHundredThirteenDG_7369 : Nat.Prime 7369 := by norm_num

private theorem prime_oneHundredThirteenDG_7457 : Nat.Prime 7457 := by norm_num

private theorem prime_oneHundredThirteenDG_7559 : Nat.Prime 7559 := by norm_num

private theorem prime_oneHundredThirteenDG_7591 : Nat.Prime 7591 := by norm_num

private theorem prime_oneHundredThirteenDG_7639 : Nat.Prime 7639 := by norm_num

private theorem prime_oneHundredThirteenDG_7717 : Nat.Prime 7717 := by norm_num

private theorem prime_oneHundredThirteenDG_7723 : Nat.Prime 7723 := by norm_num

private theorem prime_oneHundredThirteenDG_8747 : Nat.Prime 8747 := by norm_num

private theorem prime_oneHundredThirteenDG_9007 : Nat.Prime 9007 := by norm_num

private theorem prime_oneHundredThirteenDG_9161 : Nat.Prime 9161 := by norm_num

private theorem prime_oneHundredThirteenDG_9181 : Nat.Prime 9181 := by norm_num

private theorem prime_oneHundredThirteenDG_9421 : Nat.Prime 9421 := by norm_num

private theorem prime_oneHundredThirteenDG_9479 : Nat.Prime 9479 := by norm_num

private theorem prime_oneHundredThirteenDG_9829 : Nat.Prime 9829 := by norm_num

private theorem prime_oneHundredThirteenDG_10039 : Nat.Prime 10039 := by norm_num

private theorem prime_oneHundredThirteenDG_10141 : Nat.Prime 10141 := by norm_num

private theorem prime_oneHundredThirteenDG_10243 : Nat.Prime 10243 := by norm_num

private theorem prime_oneHundredThirteenDG_10853 : Nat.Prime 10853 := by norm_num

private theorem prime_oneHundredThirteenDG_10979 : Nat.Prime 10979 := by norm_num

private theorem prime_oneHundredThirteenDG_11317 : Nat.Prime 11317 := by norm_num

private theorem prime_oneHundredThirteenDG_11503 : Nat.Prime 11503 := by norm_num

private theorem prime_oneHundredThirteenDG_12289 : Nat.Prime 12289 := by norm_num

private theorem prime_oneHundredThirteenDG_12343 : Nat.Prime 12343 := by norm_num

private theorem prime_oneHundredThirteenDG_12619 : Nat.Prime 12619 := by norm_num

private theorem prime_oneHundredThirteenDG_12923 : Nat.Prime 12923 := by norm_num

private theorem prime_oneHundredThirteenDG_14389 : Nat.Prime 14389 := by norm_num

private theorem prime_oneHundredThirteenDG_14887 : Nat.Prime 14887 := by norm_num

private theorem prime_oneHundredThirteenDG_15263 : Nat.Prime 15263 := by norm_num

private theorem prime_oneHundredThirteenDG_17029 : Nat.Prime 17029 := by norm_num

private theorem prime_oneHundredThirteenDG_17099 : Nat.Prime 17099 := by norm_num

private theorem prime_oneHundredThirteenDG_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredThirteenDG_17389 : Nat.Prime 17389 := by norm_num

private theorem prime_oneHundredThirteenDG_17483 : Nat.Prime 17483 := by norm_num

private theorem prime_oneHundredThirteenDG_17623 : Nat.Prime 17623 := by norm_num

private theorem prime_oneHundredThirteenDG_17749 : Nat.Prime 17749 := by norm_num

private theorem prime_oneHundredThirteenDG_18583 : Nat.Prime 18583 := by norm_num

private theorem prime_oneHundredThirteenDG_18979 : Nat.Prime 18979 := by norm_num

private theorem prime_oneHundredThirteenDG_19141 : Nat.Prime 19141 := by norm_num

private theorem prime_oneHundredThirteenDG_19301 : Nat.Prime 19301 := by norm_num

private theorem prime_oneHundredThirteenDG_20101 : Nat.Prime 20101 := by norm_num

private theorem prime_oneHundredThirteenDG_20389 : Nat.Prime 20389 := by norm_num

private theorem prime_oneHundredThirteenDG_20627 : Nat.Prime 20627 := by norm_num

private theorem prime_oneHundredThirteenDG_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredThirteenDG_20807 : Nat.Prime 20807 := by norm_num

private theorem prime_oneHundredThirteenDG_21937 : Nat.Prime 21937 := by norm_num

private theorem prime_oneHundredThirteenDG_23189 : Nat.Prime 23189 := by norm_num

private theorem prime_oneHundredThirteenDG_23563 : Nat.Prime 23563 := by norm_num

private theorem prime_oneHundredThirteenDG_23599 : Nat.Prime 23599 := by norm_num

private theorem prime_oneHundredThirteenDG_23929 : Nat.Prime 23929 := by norm_num

private theorem prime_oneHundredThirteenDG_25391 : Nat.Prime 25391 := by norm_num

private theorem prime_oneHundredThirteenDG_25639 : Nat.Prime 25639 := by norm_num

private theorem prime_oneHundredThirteenDG_28111 : Nat.Prime 28111 := by norm_num

private theorem prime_oneHundredThirteenDG_29137 : Nat.Prime 29137 := by norm_num

private theorem prime_oneHundredThirteenDG_29179 : Nat.Prime 29179 := by norm_num

private theorem prime_oneHundredThirteenDG_29573 : Nat.Prime 29573 := by norm_num

private theorem prime_oneHundredThirteenDG_29927 : Nat.Prime 29927 := by norm_num

private theorem prime_oneHundredThirteenDG_30109 : Nat.Prime 30109 := by norm_num

private theorem prime_oneHundredThirteenDG_30529 : Nat.Prime 30529 := by norm_num

private theorem prime_oneHundredThirteenDG_33199 : Nat.Prime 33199 := by norm_num

private theorem prime_oneHundredThirteenDG_35423 : Nat.Prime 35423 := by norm_num

private theorem prime_oneHundredThirteenDG_36599 : Nat.Prime 36599 := by norm_num

private theorem prime_oneHundredThirteenDG_37951 : Nat.Prime 37951 := by norm_num

private theorem prime_oneHundredThirteenDG_38449 : Nat.Prime 38449 := by norm_num

private theorem prime_oneHundredThirteenDG_39419 : Nat.Prime 39419 := by norm_num

private theorem prime_oneHundredThirteenDG_40591 : Nat.Prime 40591 := by norm_num

private theorem prime_oneHundredThirteenDG_41849 : Nat.Prime 41849 := by norm_num

private theorem prime_oneHundredThirteenDG_43319 : Nat.Prime 43319 := by norm_num

private theorem prime_oneHundredThirteenDG_43801 : Nat.Prime 43801 := by norm_num

private theorem prime_oneHundredThirteenDG_43973 : Nat.Prime 43973 := by norm_num

private theorem prime_oneHundredThirteenDG_46337 : Nat.Prime 46337 := by norm_num

private theorem prime_oneHundredThirteenDG_47947 : Nat.Prime 47947 := by norm_num

private theorem prime_oneHundredThirteenDG_48131 : Nat.Prime 48131 := by norm_num

private theorem prime_oneHundredThirteenDG_52361 : Nat.Prime 52361 := by norm_num

private theorem prime_oneHundredThirteenDG_52757 : Nat.Prime 52757 := by norm_num

private theorem prime_oneHundredThirteenDG_56957 : Nat.Prime 56957 := by norm_num

private theorem prime_oneHundredThirteenDG_60289 : Nat.Prime 60289 := by norm_num

private theorem prime_oneHundredThirteenDG_61231 : Nat.Prime 61231 := by norm_num

private theorem prime_oneHundredThirteenDG_65761 : Nat.Prime 65761 := by norm_num

private theorem prime_oneHundredThirteenDG_69119 : Nat.Prime 69119 := by norm_num

private theorem prime_oneHundredThirteenDG_70921 : Nat.Prime 70921 := by norm_num

private theorem prime_oneHundredThirteenDG_71353 : Nat.Prime 71353 := by norm_num

private theorem prime_oneHundredThirteenDG_72383 : Nat.Prime 72383 := by norm_num

private theorem prime_oneHundredThirteenDG_74891 : Nat.Prime 74891 := by norm_num

private theorem prime_oneHundredThirteenDG_78857 : Nat.Prime 78857 := by norm_num

private theorem prime_oneHundredThirteenDG_80953 : Nat.Prime 80953 := by norm_num

private theorem prime_oneHundredThirteenDG_81043 : Nat.Prime 81043 := by norm_num

private theorem prime_oneHundredThirteenDG_89317 : Nat.Prime 89317 := by norm_num

private theorem prime_oneHundredThirteenDG_99719 : Nat.Prime 99719 := by norm_num

private theorem prime_oneHundredThirteenDG_99761 : Nat.Prime 99761 := by norm_num

private theorem prime_oneHundredThirteenDG_102079 : Nat.Prime 102079 := by norm_num

private theorem prime_oneHundredThirteenDG_107053 : Nat.Prime 107053 := by norm_num

private theorem prime_oneHundredThirteenDG_111493 : Nat.Prime 111493 := by norm_num

private theorem prime_oneHundredThirteenDG_111509 : Nat.Prime 111509 := by norm_num

private theorem prime_oneHundredThirteenDG_113039 : Nat.Prime 113039 := by norm_num

private theorem prime_oneHundredThirteenDG_113159 : Nat.Prime 113159 := by norm_num

private theorem prime_oneHundredThirteenDG_120503 : Nat.Prime 120503 := by norm_num

private theorem prime_oneHundredThirteenDG_126641 : Nat.Prime 126641 := by norm_num

private theorem prime_oneHundredThirteenDG_131743 : Nat.Prime 131743 := by norm_num

private theorem prime_oneHundredThirteenDG_140551 : Nat.Prime 140551 := by norm_num

private theorem prime_oneHundredThirteenDG_141907 : Nat.Prime 141907 := by norm_num

private theorem prime_oneHundredThirteenDG_142657 : Nat.Prime 142657 := by norm_num

private theorem prime_oneHundredThirteenDG_155461 : Nat.Prime 155461 := by norm_num

private theorem prime_oneHundredThirteenDG_163637 : Nat.Prime 163637 := by norm_num

private theorem prime_oneHundredThirteenDG_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredThirteenDG_180317 : Nat.Prime 180317 := by norm_num

private theorem prime_oneHundredThirteenDG_182821 : Nat.Prime 182821 := by norm_num

private theorem prime_oneHundredThirteenDG_186157 : Nat.Prime 186157 := by norm_num

private theorem prime_oneHundredThirteenDG_187349 : Nat.Prime 187349 := by norm_num

private theorem prime_oneHundredThirteenDG_190577 : Nat.Prime 190577 := by norm_num

private theorem prime_oneHundredThirteenDG_193871 : Nat.Prime 193871 := by norm_num

private theorem prime_oneHundredThirteenDG_197969 : Nat.Prime 197969 := by norm_num

private theorem prime_oneHundredThirteenDG_202109 : Nat.Prime 202109 := by norm_num

private theorem prime_oneHundredThirteenDG_208991 : Nat.Prime 208991 := by norm_num

private theorem prime_oneHundredThirteenDG_225769 : Nat.Prime 225769 := by norm_num

private theorem prime_oneHundredThirteenDG_228731 : Nat.Prime 228731 := by norm_num

private theorem prime_oneHundredThirteenDG_231109 : Nat.Prime 231109 := by norm_num

private theorem prime_oneHundredThirteenDG_242101 : Nat.Prime 242101 := by norm_num

private theorem prime_oneHundredThirteenDG_250841 : Nat.Prime 250841 := by norm_num

private theorem prime_oneHundredThirteenDG_258659 : Nat.Prime 258659 := by norm_num

private theorem prime_oneHundredThirteenDG_268493 : Nat.Prime 268493 := by norm_num

private theorem prime_oneHundredThirteenDG_277007 : Nat.Prime 277007 := by norm_num

private theorem prime_oneHundredThirteenDG_284897 : Nat.Prime 284897 := by norm_num

private theorem prime_oneHundredThirteenDG_292141 : Nat.Prime 292141 := by norm_num

private theorem prime_oneHundredThirteenDG_326113 : Nat.Prime 326113 := by norm_num

private theorem prime_oneHundredThirteenDG_330133 : Nat.Prime 330133 := by norm_num

private theorem prime_oneHundredThirteenDG_331241 : Nat.Prime 331241 := by norm_num

private theorem prime_oneHundredThirteenDG_333721 : Nat.Prime 333721 := by norm_num

private theorem prime_oneHundredThirteenDG_334793 : Nat.Prime 334793 := by norm_num

private theorem prime_oneHundredThirteenDG_351059 : Nat.Prime 351059 := by norm_num

private theorem prime_oneHundredThirteenDG_351529 : Nat.Prime 351529 := by norm_num

private theorem prime_oneHundredThirteenDG_363269 : Nat.Prime 363269 := by norm_num

private theorem prime_oneHundredThirteenDG_367519 : Nat.Prime 367519 := by norm_num

private theorem prime_oneHundredThirteenDG_374083 : Nat.Prime 374083 := by norm_num

private theorem prime_oneHundredThirteenDG_377963 : Nat.Prime 377963 := by norm_num

private theorem prime_oneHundredThirteenDG_381061 : Nat.Prime 381061 := by norm_num

private theorem prime_oneHundredThirteenDG_403547 : Nat.Prime 403547 := by norm_num

private theorem prime_oneHundredThirteenDG_404323 : Nat.Prime 404323 := by norm_num

private theorem prime_oneHundredThirteenDG_405871 : Nat.Prime 405871 := by norm_num

private theorem prime_oneHundredThirteenDG_418069 : Nat.Prime 418069 := by norm_num

private theorem prime_oneHundredThirteenDG_425417 : Nat.Prime 425417 := by norm_num

private theorem prime_oneHundredThirteenDG_429971 : Nat.Prime 429971 := by norm_num

private theorem prime_oneHundredThirteenDG_513269 : Nat.Prime 513269 := by norm_num

private theorem prime_oneHundredThirteenDG_517229 : Nat.Prime 517229 := by norm_num

private theorem prime_oneHundredThirteenDG_611953 : Nat.Prime 611953 := by norm_num

private theorem prime_oneHundredThirteenDG_616391 : Nat.Prime 616391 := by norm_num

private theorem prime_oneHundredThirteenDG_636553 : Nat.Prime 636553 := by norm_num

private theorem prime_oneHundredThirteenDG_650269 : Nat.Prime 650269 := by norm_num

private theorem prime_oneHundredThirteenDG_697637 : Nat.Prime 697637 := by norm_num

private theorem prime_oneHundredThirteenDG_698261 : Nat.Prime 698261 := by norm_num

private theorem prime_oneHundredThirteenDG_755617 : Nat.Prime 755617 := by norm_num

private theorem prime_oneHundredThirteenDG_868111 : Nat.Prime 868111 := by norm_num

private theorem prime_oneHundredThirteenDG_903757 : Nat.Prime 903757 := by norm_num

private theorem prime_oneHundredThirteenDG_913039 : Nat.Prime 913039 := by norm_num

private theorem prime_oneHundredThirteenDG_916339 : Nat.Prime 916339 := by norm_num

private theorem prime_oneHundredThirteenDG_919081 : Nat.Prime 919081 := by norm_num

private theorem prime_oneHundredThirteenDG_970147 : Nat.Prime 970147 := by norm_num

private theorem prime_oneHundredThirteenDG_1027489 : Nat.Prime 1027489 := by norm_num

private theorem prime_oneHundredThirteenDG_1078411 : Nat.Prime 1078411 := by norm_num

private theorem prime_oneHundredThirteenDG_1171699 : Nat.Prime 1171699 := by norm_num

private theorem prime_oneHundredThirteenDG_1177987 : Nat.Prime 1177987 := by norm_num

private theorem prime_oneHundredThirteenDG_1327489 : Nat.Prime 1327489 := by norm_num

private theorem prime_oneHundredThirteenDG_1439759 : Nat.Prime 1439759 := by norm_num

private theorem prime_oneHundredThirteenDG_1481239 : Nat.Prime 1481239 := by norm_num

private theorem prime_oneHundredThirteenDG_1553597 : Nat.Prime 1553597 := by norm_num

private theorem prime_oneHundredThirteenDG_1657867 : Nat.Prime 1657867 := by norm_num

private theorem prime_oneHundredThirteenDG_1755583 : Nat.Prime 1755583 := by norm_num

private theorem prime_oneHundredThirteenDG_1795663 : Nat.Prime 1795663 := by norm_num

private theorem prime_oneHundredThirteenDG_1834069 : Nat.Prime 1834069 := by norm_num

private theorem prime_oneHundredThirteenDG_1856513 : Nat.Prime 1856513 := by norm_num

private theorem prime_oneHundredThirteenDG_1939279 : Nat.Prime 1939279 := by norm_num

private theorem prime_oneHundredThirteenDG_2045909 : Nat.Prime 2045909 := by norm_num

private theorem prime_oneHundredThirteenDG_2089357 : Nat.Prime 2089357 := by norm_num

private theorem prime_oneHundredThirteenDG_2263243 : Nat.Prime 2263243 := by norm_num

private theorem prime_oneHundredThirteenDG_2575351 : Nat.Prime 2575351 := by norm_num

private theorem prime_oneHundredThirteenDG_2585899 : Nat.Prime 2585899 := by norm_num

private theorem prime_oneHundredThirteenDG_2601349 : Nat.Prime 2601349 := by norm_num

private theorem prime_oneHundredThirteenDG_2620171 : Nat.Prime 2620171 := by norm_num

private theorem prime_oneHundredThirteenDG_2888059 : Nat.Prime 2888059 := by norm_num

private theorem prime_oneHundredThirteenDG_3168941 : Nat.Prime 3168941 := by norm_num

private theorem prime_oneHundredThirteenDG_3208811 : Nat.Prime 3208811 := by norm_num

private theorem prime_oneHundredThirteenDG_3223547 : Nat.Prime 3223547 := by norm_num

private theorem prime_oneHundredThirteenDG_3407351 : Nat.Prime 3407351 := by norm_num

private theorem prime_oneHundredThirteenDG_3528659 : Nat.Prime 3528659 := by norm_num

private theorem prime_oneHundredThirteenDG_3759221 : Nat.Prime 3759221 := by norm_num

private theorem prime_oneHundredThirteenDG_3767831 : Nat.Prime 3767831 := by norm_num

private theorem prime_oneHundredThirteenDG_3779443 : Nat.Prime 3779443 := by norm_num

private theorem prime_oneHundredThirteenDG_4188739 : Nat.Prime 4188739 := by norm_num

private theorem prime_oneHundredThirteenDG_4334593 : Nat.Prime 4334593 := by norm_num

private theorem prime_oneHundredThirteenDG_4398707 : Nat.Prime 4398707 := by norm_num

private theorem prime_oneHundredThirteenDG_4404817 : Nat.Prime 4404817 := by norm_num

private theorem prime_oneHundredThirteenDG_4814503 : Nat.Prime 4814503 := by norm_num

private theorem prime_oneHundredThirteenDG_5011843 : Nat.Prime 5011843 := by norm_num

private theorem prime_oneHundredThirteenDG_5168279 : Nat.Prime 5168279 := by norm_num

private theorem prime_oneHundredThirteenDG_5294539 : Nat.Prime 5294539 := by norm_num

private theorem prime_oneHundredThirteenDG_5304661 : Nat.Prime 5304661 := by norm_num

private theorem prime_oneHundredThirteenDG_5653993 : Nat.Prime 5653993 := by norm_num

private theorem prime_oneHundredThirteenDG_6231437 : Nat.Prime 6231437 := by norm_num

private theorem prime_oneHundredThirteenDG_6466367 : Nat.Prime 6466367 := by norm_num

private theorem prime_oneHundredThirteenDG_6539807 : Nat.Prime 6539807 := by norm_num

private theorem prime_oneHundredThirteenDG_6551423 : Nat.Prime 6551423 := by norm_num

private theorem prime_oneHundredThirteenDG_7537561 : Nat.Prime 7537561 := by norm_num

private theorem prime_oneHundredThirteenDG_7784527 : Nat.Prime 7784527 := by norm_num

private theorem prime_oneHundredThirteenDG_7863619 : Nat.Prime 7863619 := by norm_num

private theorem prime_oneHundredThirteenDG_8557937 : Nat.Prime 8557937 := by norm_num

private theorem prime_oneHundredThirteenDG_8656727 : Nat.Prime 8656727 := by norm_num

private theorem prime_oneHundredThirteenDG_9131443 : Nat.Prime 9131443 := by norm_num

private theorem prime_oneHundredThirteenDG_9224521 : Nat.Prime 9224521 := by norm_num

private theorem prime_oneHundredThirteenDG_9509399 : Nat.Prime 9509399 := by norm_num

private theorem prime_oneHundredThirteenDG_9622489 : Nat.Prime 9622489 := by norm_num

private theorem prime_oneHundredThirteenDG_9635267 : Nat.Prime 9635267 := by norm_num

private theorem prime_oneHundredThirteenDG_10023397 : Nat.Prime 10023397 := by norm_num

private theorem prime_oneHundredThirteenDG_10101659 : Nat.Prime 10101659 := by norm_num

private theorem prime_oneHundredThirteenDG_10492411 : Nat.Prime 10492411 := by norm_num

private theorem prime_oneHundredThirteenDG_10662461 : Nat.Prime 10662461 := by norm_num

private theorem prime_oneHundredThirteenDG_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredThirteenDG_11409613 : Nat.Prime 11409613 := by norm_num

private theorem prime_oneHundredThirteenDG_12824387 : Nat.Prime 12824387 := by norm_num

private theorem prime_oneHundredThirteenDG_12845453 : Nat.Prime 12845453 := by norm_num

private theorem prime_oneHundredThirteenDG_13693283 : Nat.Prime 13693283 := by norm_num

private theorem prime_oneHundredThirteenDG_13827431 : Nat.Prime 13827431 := by norm_num

private theorem prime_oneHundredThirteenDG_14989493 : Nat.Prime 14989493 := by norm_num

private theorem prime_oneHundredThirteenDG_15989429 : Nat.Prime 15989429 := by norm_num

private theorem prime_oneHundredThirteenDG_16109939 : Nat.Prime 16109939 := by norm_num

private theorem prime_oneHundredThirteenDG_17288113 : Nat.Prime 17288113 := by norm_num

private theorem prime_oneHundredThirteenDG_17489149 : Nat.Prime 17489149 := by norm_num

private theorem prime_oneHundredThirteenDG_17519071 : Nat.Prime 17519071 := by norm_num

private theorem prime_oneHundredThirteenDG_18973237 : Nat.Prime 18973237 := by norm_num

private theorem prime_oneHundredThirteenDG_19989209 : Nat.Prime 19989209 := by norm_num

private theorem prime_oneHundredThirteenDG_20132201 : Nat.Prime 20132201 := by norm_num

private theorem prime_oneHundredThirteenDG_25548707 : Nat.Prime 25548707 := by norm_num

private theorem prime_oneHundredThirteenDG_26388149 : Nat.Prime 26388149 := by norm_num

private theorem prime_oneHundredThirteenDG_27750607 : Nat.Prime 27750607 := by norm_num

private theorem prime_oneHundredThirteenDG_28307333 : Nat.Prime 28307333 := by norm_num

private theorem prime_oneHundredThirteenDG_28429001 : Nat.Prime 28429001 := by norm_num

private theorem prime_oneHundredThirteenDG_31806641 : Nat.Prime 31806641 := by
  apply lucas_primality 31806641 (3 : ZMod 31806641)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (151, 1), (2633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (151, 1), (2633, 1)] : List FactorBlock).map factorBlockValue).prod) = 31806641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_151
      · exact prime_oneHundredThirteenDG_2633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31806641) ^ 15903320 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31806641) ^ 6361328 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31806641) ^ 210640 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31806641) ^ 12080 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_32140627 : Nat.Prime 32140627 := by
  apply lucas_primality 32140627 (3 : ZMod 32140627)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (547, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (547, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) = 32140627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_547
      · exact prime_oneHundredThirteenDG_1399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32140627) ^ 16070313 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 32140627) ^ 10713542 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 32140627) ^ 4591518 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 32140627) ^ 58758 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 32140627) ^ 22974 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_33481913 : Nat.Prime 33481913 := by
  apply lucas_primality 33481913 (3 : ZMod 33481913)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (102079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (102079, 1)] : List FactorBlock).map factorBlockValue).prod) = 33481913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_41
      · exact prime_oneHundredThirteenDG_102079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 33481913) ^ 16740956 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 33481913) ^ 816632 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 33481913) ^ 328 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_33516529 : Nat.Prime 33516529 := by
  apply lucas_primality 33516529 (22 : ZMod 33516529)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (698261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (698261, 1)] : List FactorBlock).map factorBlockValue).prod) = 33516529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_698261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (22 : ZMod 33516529) ^ 16758264 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (22 : ZMod 33516529) ^ 11172176 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (22 : ZMod 33516529) ^ 48 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_37029001 : Nat.Prime 37029001 := by
  apply lucas_primality 37029001 (19 : ZMod 37029001)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (12343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (12343, 1)] : List FactorBlock).map factorBlockValue).prod) = 37029001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_12343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 37029001) ^ 18514500 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (19 : ZMod 37029001) ^ 12343000 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (19 : ZMod 37029001) ^ 7405800 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (19 : ZMod 37029001) ^ 3000 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_44970371 : Nat.Prime 44970371 := by
  apply lucas_primality 44970371 (2 : ZMod 44970371)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (263, 1), (17099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (263, 1), (17099, 1)] : List FactorBlock).map factorBlockValue).prod) = 44970371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_263
      · exact prime_oneHundredThirteenDG_17099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44970371) ^ 22485185 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44970371) ^ 8994074 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44970371) ^ 170990 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44970371) ^ 2630 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_45014833 : Nat.Prime 45014833 := by
  apply lucas_primality 45014833 (10 : ZMod 45014833)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (79, 1), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (79, 1), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) = 45014833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_79
      · exact prime_oneHundredThirteenDG_1319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 45014833) ^ 22507416 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 45014833) ^ 15004944 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 45014833) ^ 569808 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 45014833) ^ 34128 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_46100473 : Nat.Prime 46100473 := by
  apply lucas_primality 46100473 (59 : ZMod 46100473)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (31, 1), (43, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (31, 1), (43, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) = 46100473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_31
      · exact prime_oneHundredThirteenDG_43
      · exact prime_oneHundredThirteenDG_131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (59 : ZMod 46100473) ^ 23050236 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (59 : ZMod 46100473) ^ 15366824 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (59 : ZMod 46100473) ^ 4190952 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (59 : ZMod 46100473) ^ 1487112 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (59 : ZMod 46100473) ^ 1072104 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (59 : ZMod 46100473) ^ 351912 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_46420277 : Nat.Prime 46420277 := by
  apply lucas_primality 46420277 (2 : ZMod 46420277)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1657867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1657867, 1)] : List FactorBlock).map factorBlockValue).prod) = 46420277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_1657867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46420277) ^ 23210138 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 46420277) ^ 6631468 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 46420277) ^ 28 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_49511083 : Nat.Prime 49511083 := by
  apply lucas_primality 49511083 (2 : ZMod 49511083)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (113039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (113039, 1)] : List FactorBlock).map factorBlockValue).prod) = 49511083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_73
      · exact prime_oneHundredThirteenDG_113039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 49511083) ^ 24755541 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49511083) ^ 16503694 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49511083) ^ 678234 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49511083) ^ 438 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_49920851 : Nat.Prime 49920851 := by
  apply lucas_primality 49920851 (2 : ZMod 49920851)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (31, 1), (43, 1), (107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (31, 1), (43, 1), (107, 1)] : List FactorBlock).map factorBlockValue).prod) = 49920851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_31
      · exact prime_oneHundredThirteenDG_43
      · exact prime_oneHundredThirteenDG_107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49920851) ^ 24960425 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49920851) ^ 9984170 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49920851) ^ 7131550 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49920851) ^ 1610350 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49920851) ^ 1160950 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49920851) ^ 466550 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_50921551 : Nat.Prime 50921551 := by
  apply lucas_primality 50921551 (13 : ZMod 50921551)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (113159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (113159, 1)] : List FactorBlock).map factorBlockValue).prod) = 50921551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_113159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 50921551) ^ 25460775 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 50921551) ^ 16973850 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 50921551) ^ 10184310 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 50921551) ^ 450 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_51763729 : Nat.Prime 51763729 := by
  apply lucas_primality 51763729 (7 : ZMod 51763729)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1078411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1078411, 1)] : List FactorBlock).map factorBlockValue).prod) = 51763729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_1078411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 51763729) ^ 25881864 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 51763729) ^ 17254576 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 51763729) ^ 48 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_53506777 : Nat.Prime 53506777 := by
  apply lucas_primality 53506777 (10 : ZMod 53506777)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (197, 1), (11317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (197, 1), (11317, 1)] : List FactorBlock).map factorBlockValue).prod) = 53506777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_197
      · exact prime_oneHundredThirteenDG_11317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 53506777) ^ 26753388 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 53506777) ^ 17835592 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 53506777) ^ 271608 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 53506777) ^ 4728 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_55695391 : Nat.Prime 55695391 := by
  apply lucas_primality 55695391 (6 : ZMod 55695391)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1856513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1856513, 1)] : List FactorBlock).map factorBlockValue).prod) = 55695391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_1856513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 55695391) ^ 27847695 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 55695391) ^ 18565130 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 55695391) ^ 11139078 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 55695391) ^ 30 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_58178371 : Nat.Prime 58178371 := by
  apply lucas_primality 58178371 (2 : ZMod 58178371)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1939279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1939279, 1)] : List FactorBlock).map factorBlockValue).prod) = 58178371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_1939279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58178371) ^ 29089185 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 58178371) ^ 19392790 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 58178371) ^ 11635674 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 58178371) ^ 30 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_62419207 : Nat.Prime 62419207 := by
  apply lucas_primality 62419207 (3 : ZMod 62419207)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (611953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (611953, 1)] : List FactorBlock).map factorBlockValue).prod) = 62419207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_611953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 62419207) ^ 31209603 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 62419207) ^ 20806402 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 62419207) ^ 3671718 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 62419207) ^ 102 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_62775767 : Nat.Prime 62775767 := by
  apply lucas_primality 62775767 (5 : ZMod 62775767)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (429971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (429971, 1)] : List FactorBlock).map factorBlockValue).prod) = 62775767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_73
      · exact prime_oneHundredThirteenDG_429971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 62775767) ^ 31387883 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 62775767) ^ 859942 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 62775767) ^ 146 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_63719473 : Nat.Prime 63719473 := by
  apply lucas_primality 63719473 (5 : ZMod 63719473)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1327489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1327489, 1)] : List FactorBlock).map factorBlockValue).prod) = 63719473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_1327489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 63719473) ^ 31859736 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 63719473) ^ 21239824 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 63719473) ^ 48 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_64018249 : Nat.Prime 64018249 := by
  apply lucas_primality 64018249 (17 : ZMod 64018249)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (381061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (381061, 1)] : List FactorBlock).map factorBlockValue).prod) = 64018249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_381061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 64018249) ^ 32009124 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (17 : ZMod 64018249) ^ 21339416 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (17 : ZMod 64018249) ^ 9145464 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (17 : ZMod 64018249) ^ 168 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_64470941 : Nat.Prime 64470941 := by
  apply lucas_primality 64470941 (2 : ZMod 64470941)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3223547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3223547, 1)] : List FactorBlock).map factorBlockValue).prod) = 64470941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_3223547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 64470941) ^ 32235470 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 64470941) ^ 12894188 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 64470941) ^ 20 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_65530247 : Nat.Prime 65530247 := by
  apply lucas_primality 65530247 (5 : ZMod 65530247)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1607, 1), (20389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1607, 1), (20389, 1)] : List FactorBlock).map factorBlockValue).prod) = 65530247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_1607
      · exact prime_oneHundredThirteenDG_20389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 65530247) ^ 32765123 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 65530247) ^ 40778 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 65530247) ^ 3214 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_71955683 : Nat.Prime 71955683 := by
  apply lucas_primality 71955683 (2 : ZMod 71955683)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2069, 1), (17389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2069, 1), (17389, 1)] : List FactorBlock).map factorBlockValue).prod) = 71955683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_2069
      · exact prime_oneHundredThirteenDG_17389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 71955683) ^ 35977841 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 71955683) ^ 34778 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 71955683) ^ 4138 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_79513477 : Nat.Prime 79513477 := by
  apply lucas_primality 79513477 (2 : ZMod 79513477)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (29, 1), (4663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (29, 1), (4663, 1)] : List FactorBlock).map factorBlockValue).prod) = 79513477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_29
      · exact prime_oneHundredThirteenDG_4663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79513477) ^ 39756738 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 79513477) ^ 26504492 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 79513477) ^ 11359068 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 79513477) ^ 2741844 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 79513477) ^ 17052 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_82630901 : Nat.Prime 82630901 := by
  apply lucas_primality 82630901 (2 : ZMod 82630901)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 2), (6829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 2), (6829, 1)] : List FactorBlock).map factorBlockValue).prod) = 82630901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_6829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 82630901) ^ 41315450 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 82630901) ^ 16526180 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 82630901) ^ 7511900 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 82630901) ^ 12100 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_94502411 : Nat.Prime 94502411 := by
  apply lucas_primality 94502411 (2 : ZMod 94502411)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (769, 1), (12289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (769, 1), (12289, 1)] : List FactorBlock).map factorBlockValue).prod) = 94502411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_769
      · exact prime_oneHundredThirteenDG_12289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 94502411) ^ 47251205 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 94502411) ^ 18900482 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 94502411) ^ 122890 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 94502411) ^ 7690 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_116443163 : Nat.Prime 116443163 := by
  apply lucas_primality 116443163 (2 : ZMod 116443163)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1931, 1), (2741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1931, 1), (2741, 1)] : List FactorBlock).map factorBlockValue).prod) = 116443163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_1931
      · exact prime_oneHundredThirteenDG_2741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 116443163) ^ 58221581 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 116443163) ^ 10585742 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 116443163) ^ 60302 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 116443163) ^ 42482 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_122939617 : Nat.Prime 122939617 := by
  apply lucas_primality 122939617 (7 : ZMod 122939617)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (89, 1), (14389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (89, 1), (14389, 1)] : List FactorBlock).map factorBlockValue).prod) = 122939617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_89
      · exact prime_oneHundredThirteenDG_14389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 122939617) ^ 61469808 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 122939617) ^ 40979872 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 122939617) ^ 1381344 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 122939617) ^ 8544 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_124862783 : Nat.Prime 124862783 := by
  apply lucas_primality 124862783 (5 : ZMod 124862783)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1151, 1), (4931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1151, 1), (4931, 1)] : List FactorBlock).map factorBlockValue).prod) = 124862783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_1151
      · exact prime_oneHundredThirteenDG_4931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 124862783) ^ 62431391 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 124862783) ^ 11351162 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 124862783) ^ 108482 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 124862783) ^ 25322 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_130151191 : Nat.Prime 130151191 := by
  apply lucas_primality 130151191 (3 : ZMod 130151191)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (333721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (333721, 1)] : List FactorBlock).map factorBlockValue).prod) = 130151191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_333721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 130151191) ^ 65075595 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 130151191) ^ 43383730 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 130151191) ^ 26030238 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 130151191) ^ 10011630 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 130151191) ^ 390 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_134578331 : Nat.Prime 134578331 := by
  apply lucas_primality 134578331 (2 : ZMod 134578331)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (359, 1), (1973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (359, 1), (1973, 1)] : List FactorBlock).map factorBlockValue).prod) = 134578331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_19
      · exact prime_oneHundredThirteenDG_359
      · exact prime_oneHundredThirteenDG_1973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 134578331) ^ 67289165 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 134578331) ^ 26915666 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 134578331) ^ 7083070 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 134578331) ^ 374870 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 134578331) ^ 68210 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_151031693 : Nat.Prime 151031693 := by
  apply lucas_primality 151031693 (3 : ZMod 151031693)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1307, 1), (4127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1307, 1), (4127, 1)] : List FactorBlock).map factorBlockValue).prod) = 151031693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_1307
      · exact prime_oneHundredThirteenDG_4127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 151031693) ^ 75515846 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 151031693) ^ 21575956 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 151031693) ^ 115556 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 151031693) ^ 36596 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_161306503 : Nat.Prime 161306503 := by
  apply lucas_primality 161306503 (3 : ZMod 161306503)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (43, 1), (89317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (43, 1), (89317, 1)] : List FactorBlock).map factorBlockValue).prod) = 161306503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_43
      · exact prime_oneHundredThirteenDG_89317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 161306503) ^ 80653251 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 161306503) ^ 53768834 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 161306503) ^ 23043786 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 161306503) ^ 3751314 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 161306503) ^ 1806 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_168571499 : Nat.Prime 168571499 := by
  apply lucas_primality 168571499 (2 : ZMod 168571499)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (223, 1), (377963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (223, 1), (377963, 1)] : List FactorBlock).map factorBlockValue).prod) = 168571499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_223
      · exact prime_oneHundredThirteenDG_377963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 168571499) ^ 84285749 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 168571499) ^ 755926 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 168571499) ^ 446 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_174124891 : Nat.Prime 174124891 := by
  apply lucas_primality 174124891 (3 : ZMod 174124891)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (227, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (227, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) = 174124891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_227
      · exact prime_oneHundredThirteenDG_947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 174124891) ^ 87062445 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 174124891) ^ 58041630 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 174124891) ^ 34824978 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 174124891) ^ 767070 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 174124891) ^ 183870 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_221268989 : Nat.Prime 221268989 := by
  apply lucas_primality 221268989 (2 : ZMod 221268989)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (167, 1), (331241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (167, 1), (331241, 1)] : List FactorBlock).map factorBlockValue).prod) = 221268989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_167
      · exact prime_oneHundredThirteenDG_331241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 221268989) ^ 110634494 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 221268989) ^ 1324964 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 221268989) ^ 668 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_235624717 : Nat.Prime 235624717 := by
  apply lucas_primality 235624717 (2 : ZMod 235624717)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (83, 1), (78857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (83, 1), (78857, 1)] : List FactorBlock).map factorBlockValue).prod) = 235624717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_83
      · exact prime_oneHundredThirteenDG_78857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 235624717) ^ 117812358 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 235624717) ^ 78541572 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 235624717) ^ 2838852 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 235624717) ^ 2988 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_238299331 : Nat.Prime 238299331 := by
  apply lucas_primality 238299331 (2 : ZMod 238299331)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (418069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (418069, 1)] : List FactorBlock).map factorBlockValue).prod) = 238299331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_19
      · exact prime_oneHundredThirteenDG_418069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 238299331) ^ 119149665 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 238299331) ^ 79433110 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 238299331) ^ 47659866 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 238299331) ^ 12542070 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 238299331) ^ 570 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_239870509 : Nat.Prime 239870509 := by
  apply lucas_primality 239870509 (2 : ZMod 239870509)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19989209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19989209, 1)] : List FactorBlock).map factorBlockValue).prod) = 239870509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_19989209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 239870509) ^ 119935254 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 239870509) ^ 79956836 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 239870509) ^ 12 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_241365199 : Nat.Prime 241365199 := by
  apply lucas_primality 241365199 (3 : ZMod 241365199)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (839, 1), (47947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (839, 1), (47947, 1)] : List FactorBlock).map factorBlockValue).prod) = 241365199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_839
      · exact prime_oneHundredThirteenDG_47947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 241365199) ^ 120682599 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 241365199) ^ 80455066 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 241365199) ^ 287682 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 241365199) ^ 5034 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_279067751 : Nat.Prime 279067751 := by
  apply lucas_primality 279067751 (7 : ZMod 279067751)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (13, 1), (17, 1), (5051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (13, 1), (17, 1), (5051, 1)] : List FactorBlock).map factorBlockValue).prod) = 279067751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_5051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 279067751) ^ 139533875 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 279067751) ^ 55813550 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 279067751) ^ 21466750 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 279067751) ^ 16415750 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 279067751) ^ 55250 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_305529307 : Nat.Prime 305529307 := by
  apply lucas_primality 305529307 (3 : ZMod 305529307)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (50921551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (50921551, 1)] : List FactorBlock).map factorBlockValue).prod) = 305529307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_50921551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 305529307) ^ 152764653 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 305529307) ^ 101843102 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 305529307) ^ 6 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_307393943 : Nat.Prime 307393943 := by
  apply lucas_primality 307393943 (5 : ZMod 307393943)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (1033, 1), (6469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (1033, 1), (6469, 1)] : List FactorBlock).map factorBlockValue).prod) = 307393943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_23
      · exact prime_oneHundredThirteenDG_1033
      · exact prime_oneHundredThirteenDG_6469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 307393943) ^ 153696971 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 307393943) ^ 13364954 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 307393943) ^ 297574 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 307393943) ^ 47518 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_313152473 : Nat.Prime 313152473 := by
  apply lucas_primality 313152473 (3 : ZMod 313152473)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (97, 1), (403547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (97, 1), (403547, 1)] : List FactorBlock).map factorBlockValue).prod) = 313152473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_97
      · exact prime_oneHundredThirteenDG_403547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 313152473) ^ 156576236 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 313152473) ^ 3228376 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 313152473) ^ 776 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_327825787 : Nat.Prime 327825787 := by
  apply lucas_primality 327825787 (2 : ZMod 327825787)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (383, 1), (142657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (383, 1), (142657, 1)] : List FactorBlock).map factorBlockValue).prod) = 327825787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_383
      · exact prime_oneHundredThirteenDG_142657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 327825787) ^ 163912893 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 327825787) ^ 109275262 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 327825787) ^ 855942 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 327825787) ^ 2298 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_366331439 : Nat.Prime 366331439 := by
  apply lucas_primality 366331439 (11 : ZMod 366331439)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (587, 1), (1493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (587, 1), (1493, 1)] : List FactorBlock).map factorBlockValue).prod) = 366331439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_19
      · exact prime_oneHundredThirteenDG_587
      · exact prime_oneHundredThirteenDG_1493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 366331439) ^ 183165719 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 366331439) ^ 33302858 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 366331439) ^ 19280602 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 366331439) ^ 624074 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 366331439) ^ 245366 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_380052599 : Nat.Prime 380052599 := by
  apply lucas_primality 380052599 (11 : ZMod 380052599)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (29, 1), (284897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (29, 1), (284897, 1)] : List FactorBlock).map factorBlockValue).prod) = 380052599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_23
      · exact prime_oneHundredThirteenDG_29
      · exact prime_oneHundredThirteenDG_284897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 380052599) ^ 190026299 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 380052599) ^ 16524026 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 380052599) ^ 13105262 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 380052599) ^ 1334 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_399366809 : Nat.Prime 399366809 := by
  apply lucas_primality 399366809 (3 : ZMod 399366809)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (49920851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (49920851, 1)] : List FactorBlock).map factorBlockValue).prod) = 399366809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_49920851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 399366809) ^ 199683404 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 399366809) ^ 8 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_404630977 : Nat.Prime 404630977 := by
  apply lucas_primality 404630977 (15 : ZMod 404630977)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (83, 1), (25391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (83, 1), (25391, 1)] : List FactorBlock).map factorBlockValue).prod) = 404630977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_83
      · exact prime_oneHundredThirteenDG_25391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 404630977) ^ 202315488 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (15 : ZMod 404630977) ^ 134876992 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (15 : ZMod 404630977) ^ 4875072 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (15 : ZMod 404630977) ^ 15936 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_533123051 : Nat.Prime 533123051 := by
  apply lucas_primality 533123051 (6 : ZMod 533123051)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (10662461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (10662461, 1)] : List FactorBlock).map factorBlockValue).prod) = 533123051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_10662461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 533123051) ^ 266561525 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 533123051) ^ 106624610 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 533123051) ^ 50 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_540475051 : Nat.Prime 540475051 := by
  apply lucas_primality 540475051 (3 : ZMod 540475051)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (17, 1), (181, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (17, 1), (181, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) = 540475051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_181
      · exact prime_oneHundredThirteenDG_1171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 540475051) ^ 270237525 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 540475051) ^ 180158350 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 540475051) ^ 108095010 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 540475051) ^ 31792650 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 540475051) ^ 2986050 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 540475051) ^ 461550 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_546281243 : Nat.Prime 546281243 := by
  apply lucas_primality 546281243 (2 : ZMod 546281243)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (71, 1), (541, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (71, 1), (541, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod) = 546281243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_71
      · exact prime_oneHundredThirteenDG_541
      · exact prime_oneHundredThirteenDG_547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 546281243) ^ 273140621 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 546281243) ^ 42021634 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 546281243) ^ 7694102 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 546281243) ^ 1009762 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 546281243) ^ 998686 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_698140453 : Nat.Prime 698140453 := by
  apply lucas_primality 698140453 (2 : ZMod 698140453)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (58178371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (58178371, 1)] : List FactorBlock).map factorBlockValue).prod) = 698140453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_58178371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 698140453) ^ 349070226 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 698140453) ^ 232713484 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 698140453) ^ 12 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_17203
      · exact prime_oneHundredThirteenDG_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_819257041 : Nat.Prime 819257041 := by
  apply lucas_primality 819257041 (13 : ZMod 819257041)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (7, 1), (53, 1), (3067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (7, 1), (53, 1), (3067, 1)] : List FactorBlock).map factorBlockValue).prod) = 819257041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_53
      · exact prime_oneHundredThirteenDG_3067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 819257041) ^ 409628520 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 819257041) ^ 273085680 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 819257041) ^ 163851408 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 819257041) ^ 117036720 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 819257041) ^ 15457680 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 819257041) ^ 267120 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1226334971 : Nat.Prime 1226334971 := by
  apply lucas_primality 1226334971 (2 : ZMod 1226334971)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (17519071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (17519071, 1)] : List FactorBlock).map factorBlockValue).prod) = 1226334971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_17519071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1226334971) ^ 613167485 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1226334971) ^ 245266994 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1226334971) ^ 175190710 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1226334971) ^ 70 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1229514271 : Nat.Prime 1229514271 := by
  apply lucas_primality 1229514271 (26 : ZMod 1229514271)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (5399, 1), (7591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (5399, 1), (7591, 1)] : List FactorBlock).map factorBlockValue).prod) = 1229514271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_5399
      · exact prime_oneHundredThirteenDG_7591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 1229514271) ^ 614757135 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (26 : ZMod 1229514271) ^ 409838090 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (26 : ZMod 1229514271) ^ 245902854 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (26 : ZMod 1229514271) ^ 227730 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (26 : ZMod 1229514271) ^ 161970 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1244981737 : Nat.Prime 1244981737 := by
  apply lucas_primality 1244981737 (5 : ZMod 1244981737)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (3257, 1), (5309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (3257, 1), (5309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1244981737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_3257
      · exact prime_oneHundredThirteenDG_5309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1244981737) ^ 622490868 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1244981737) ^ 414993912 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1244981737) ^ 382248 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1244981737) ^ 234504 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1364592049 : Nat.Prime 1364592049 := by
  apply lucas_primality 1364592049 (11 : ZMod 1364592049)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (28429001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (28429001, 1)] : List FactorBlock).map factorBlockValue).prod) = 1364592049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_28429001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1364592049) ^ 682296024 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1364592049) ^ 454864016 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1364592049) ^ 48 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1565472737 : Nat.Prime 1565472737 := by
  apply lucas_primality 1565472737 (3 : ZMod 1565472737)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (23, 1), (73, 1), (29137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (23, 1), (73, 1), (29137, 1)] : List FactorBlock).map factorBlockValue).prod) = 1565472737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_23
      · exact prime_oneHundredThirteenDG_73
      · exact prime_oneHundredThirteenDG_29137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1565472737) ^ 782736368 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1565472737) ^ 68064032 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1565472737) ^ 21444832 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1565472737) ^ 53728 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1732757941 : Nat.Prime 1732757941 := by
  apply lucas_primality 1732757941 (2 : ZMod 1732757941)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (3208811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (3208811, 1)] : List FactorBlock).map factorBlockValue).prod) = 1732757941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_3208811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1732757941) ^ 866378970 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1732757941) ^ 577585980 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1732757941) ^ 346551588 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1732757941) ^ 540 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1766017153 : Nat.Prime 1766017153 := by
  apply lucas_primality 1766017153 (7 : ZMod 1766017153)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (241, 1), (6361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (241, 1), (6361, 1)] : List FactorBlock).map factorBlockValue).prod) = 1766017153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_241
      · exact prime_oneHundredThirteenDG_6361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1766017153) ^ 883008576 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1766017153) ^ 588672384 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1766017153) ^ 7327872 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1766017153) ^ 277632 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1839635359 : Nat.Prime 1839635359 := by
  apply lucas_primality 1839635359 (3 : ZMod 1839635359)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (23, 1), (29, 2), (131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (23, 1), (29, 2), (131, 1)] : List FactorBlock).map factorBlockValue).prod) = 1839635359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_23
      · exact prime_oneHundredThirteenDG_29
      · exact prime_oneHundredThirteenDG_131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1839635359) ^ 919817679 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1839635359) ^ 613211786 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1839635359) ^ 167239578 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1839635359) ^ 79984146 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1839635359) ^ 63435702 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1839635359) ^ 14043018 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2086253237 : Nat.Prime 2086253237 := by
  apply lucas_primality 2086253237 (2 : ZMod 2086253237)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (7784527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (7784527, 1)] : List FactorBlock).map factorBlockValue).prod) = 2086253237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_67
      · exact prime_oneHundredThirteenDG_7784527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2086253237) ^ 1043126618 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2086253237) ^ 31138108 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2086253237) ^ 268 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2148403427 : Nat.Prime 2148403427 := by
  apply lucas_primality 2148403427 (2 : ZMod 2148403427)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (82630901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (82630901, 1)] : List FactorBlock).map factorBlockValue).prod) = 2148403427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_82630901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2148403427) ^ 1074201713 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2148403427) ^ 165261802 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2148403427) ^ 26 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2212913107 : Nat.Prime 2212913107 := by
  apply lucas_primality 2212913107 (5 : ZMod 2212913107)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (122939617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (122939617, 1)] : List FactorBlock).map factorBlockValue).prod) = 2212913107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_122939617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2212913107) ^ 1106456553 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2212913107) ^ 737637702 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2212913107) ^ 18 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2365805447 : Nat.Prime 2365805447 := by
  apply lucas_primality 2365805447 (5 : ZMod 2365805447)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2287, 1), (517229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2287, 1), (517229, 1)] : List FactorBlock).map factorBlockValue).prod) = 2365805447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_2287
      · exact prime_oneHundredThirteenDG_517229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2365805447) ^ 1182902723 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2365805447) ^ 1034458 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2365805447) ^ 4574 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2381352331 : Nat.Prime 2381352331 := by
  apply lucas_primality 2381352331 (3 : ZMod 2381352331)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (211, 1), (223, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (211, 1), (223, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) = 2381352331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_211
      · exact prime_oneHundredThirteenDG_223
      · exact prime_oneHundredThirteenDG_241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2381352331) ^ 1190676165 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2381352331) ^ 793784110 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2381352331) ^ 476270466 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2381352331) ^ 340193190 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2381352331) ^ 11286030 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2381352331) ^ 10678710 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2381352331) ^ 9881130 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2385404311 : Nat.Prime 2385404311 := by
  apply lucas_primality 2385404311 (6 : ZMod 2385404311)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (79513477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (79513477, 1)] : List FactorBlock).map factorBlockValue).prod) = 2385404311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_79513477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2385404311) ^ 1192702155 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 2385404311) ^ 795134770 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 2385404311) ^ 477080862 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 2385404311) ^ 30 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2588541541 : Nat.Prime 2588541541 := by
  apply lucas_primality 2588541541 (2 : ZMod 2588541541)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (31, 1), (107053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (31, 1), (107053, 1)] : List FactorBlock).map factorBlockValue).prod) = 2588541541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_31
      · exact prime_oneHundredThirteenDG_107053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2588541541) ^ 1294270770 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2588541541) ^ 862847180 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2588541541) ^ 517708308 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2588541541) ^ 199118580 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2588541541) ^ 83501340 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2588541541) ^ 24180 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2795241367 : Nat.Prime 2795241367 := by
  apply lucas_primality 2795241367 (5 : ZMod 2795241367)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (51763729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (51763729, 1)] : List FactorBlock).map factorBlockValue).prod) = 2795241367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_51763729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2795241367) ^ 1397620683 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2795241367) ^ 931747122 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2795241367) ^ 54 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_3229012529 : Nat.Prime 3229012529 := by
  apply lucas_primality 3229012529 (3 : ZMod 3229012529)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (599, 1), (48131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (599, 1), (48131, 1)] : List FactorBlock).map factorBlockValue).prod) = 3229012529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_599
      · exact prime_oneHundredThirteenDG_48131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3229012529) ^ 1614506264 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3229012529) ^ 461287504 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3229012529) ^ 5390672 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3229012529) ^ 67088 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_3258522931 : Nat.Prime 3258522931 := by
  apply lucas_primality 3258522931 (11 : ZMod 3258522931)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (23, 1), (363269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (23, 1), (363269, 1)] : List FactorBlock).map factorBlockValue).prod) = 3258522931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_23
      · exact prime_oneHundredThirteenDG_363269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3258522931) ^ 1629261465 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 3258522931) ^ 1086174310 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 3258522931) ^ 651704586 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 3258522931) ^ 250655610 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 3258522931) ^ 141674910 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 3258522931) ^ 8970 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_3814240327 : Nat.Prime 3814240327 := by
  apply lucas_primality 3814240327 (6 : ZMod 3814240327)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (1571, 1), (1831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (1571, 1), (1831, 1)] : List FactorBlock).map factorBlockValue).prod) = 3814240327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_1571
      · exact prime_oneHundredThirteenDG_1831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3814240327) ^ 1907120163 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 3814240327) ^ 1271413442 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 3814240327) ^ 293403102 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 3814240327) ^ 224367078 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 3814240327) ^ 2427906 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 3814240327) ^ 2083146 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_4145647993 : Nat.Prime 4145647993 := by
  apply lucas_primality 4145647993 (5 : ZMod 4145647993)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5737, 1), (30109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5737, 1), (30109, 1)] : List FactorBlock).map factorBlockValue).prod) = 4145647993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5737
      · exact prime_oneHundredThirteenDG_30109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4145647993) ^ 2072823996 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4145647993) ^ 1381882664 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4145647993) ^ 722616 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4145647993) ^ 137688 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_4188842719 : Nat.Prime 4188842719 := by
  apply lucas_primality 4188842719 (6 : ZMod 4188842719)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (698140453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (698140453, 1)] : List FactorBlock).map factorBlockValue).prod) = 4188842719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_698140453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 4188842719) ^ 2094421359 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 4188842719) ^ 1396280906 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 4188842719) ^ 6 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_4706319721 : Nat.Prime 4706319721 := by
  apply lucas_primality 4706319721 (7 : ZMod 4706319721)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (97, 1), (404323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (97, 1), (404323, 1)] : List FactorBlock).map factorBlockValue).prod) = 4706319721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_97
      · exact prime_oneHundredThirteenDG_404323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4706319721) ^ 2353159860 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4706319721) ^ 1568773240 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4706319721) ^ 941263944 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4706319721) ^ 48518760 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4706319721) ^ 11640 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_4792401709 : Nat.Prime 4792401709 := by
  apply lucas_primality 4792401709 (2 : ZMod 4792401709)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (399366809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (399366809, 1)] : List FactorBlock).map factorBlockValue).prod) = 4792401709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_399366809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4792401709) ^ 2396200854 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4792401709) ^ 1597467236 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4792401709) ^ 12 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_31
      · exact prime_oneHundredThirteenDG_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_7696346921 : Nat.Prime 7696346921 := by
  apply lucas_primality 7696346921 (3 : ZMod 7696346921)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (2713, 1), (70921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (2713, 1), (70921, 1)] : List FactorBlock).map factorBlockValue).prod) = 7696346921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_2713
      · exact prime_oneHundredThirteenDG_70921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7696346921) ^ 3848173460 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7696346921) ^ 1539269384 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7696346921) ^ 2836840 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7696346921) ^ 108520 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_8685589841 : Nat.Prime 8685589841 := by
  apply lucas_primality 8685589841 (6 : ZMod 8685589841)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (167, 1), (277, 1), (2347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (167, 1), (277, 1), (2347, 1)] : List FactorBlock).map factorBlockValue).prod) = 8685589841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_167
      · exact prime_oneHundredThirteenDG_277
      · exact prime_oneHundredThirteenDG_2347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8685589841) ^ 4342794920 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 8685589841) ^ 1737117968 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 8685589841) ^ 52009520 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 8685589841) ^ 31355920 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 8685589841) ^ 3700720 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_9164351773 : Nat.Prime 9164351773 := by
  apply lucas_primality 9164351773 (5 : ZMod 9164351773)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (17, 1), (263, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (17, 1), (263, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) = 9164351773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_263
      · exact prime_oneHundredThirteenDG_18979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9164351773) ^ 4582175886 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 9164351773) ^ 3054783924 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 9164351773) ^ 539079516 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 9164351773) ^ 34845444 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 9164351773) ^ 482868 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_9791363957 : Nat.Prime 9791363957 := by
  apply lucas_primality 9791363957 (2 : ZMod 9791363957)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (3907, 1), (56957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (3907, 1), (56957, 1)] : List FactorBlock).map factorBlockValue).prod) = 9791363957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_3907
      · exact prime_oneHundredThirteenDG_56957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9791363957) ^ 4895681978 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9791363957) ^ 890123996 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9791363957) ^ 2506108 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9791363957) ^ 171908 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_9919238171 : Nat.Prime 9919238171 := by
  apply lucas_primality 9919238171 (2 : ZMod 9919238171)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5501, 1), (180317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5501, 1), (180317, 1)] : List FactorBlock).map factorBlockValue).prod) = 9919238171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_5501
      · exact prime_oneHundredThirteenDG_180317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9919238171) ^ 4959619085 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9919238171) ^ 1983847634 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9919238171) ^ 1803170 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9919238171) ^ 55010 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_9946559327 : Nat.Prime 9946559327 := by
  apply lucas_primality 9946559327 (5 : ZMod 9946559327)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2473, 1), (182821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2473, 1), (182821, 1)] : List FactorBlock).map factorBlockValue).prod) = 9946559327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_2473
      · exact prime_oneHundredThirteenDG_182821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9946559327) ^ 4973279663 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 9946559327) ^ 904232666 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 9946559327) ^ 4022062 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 9946559327) ^ 54406 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_10057717069 : Nat.Prime 10057717069 := by
  apply lucas_primality 10057717069 (6 : ZMod 10057717069)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (1487, 1), (11503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (1487, 1), (11503, 1)] : List FactorBlock).map factorBlockValue).prod) = 10057717069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_1487
      · exact prime_oneHundredThirteenDG_11503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10057717069) ^ 5028858534 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 10057717069) ^ 3352572356 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 10057717069) ^ 1436816724 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 10057717069) ^ 6763764 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 10057717069) ^ 874356 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_11180965469 : Nat.Prime 11180965469 := by
  apply lucas_primality 11180965469 (2 : ZMod 11180965469)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2795241367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2795241367, 1)] : List FactorBlock).map factorBlockValue).prod) = 11180965469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_2795241367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 11180965469) ^ 5590482734 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11180965469) ^ 4 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_11692148857 : Nat.Prime 11692148857 := by
  apply lucas_primality 11692148857 (15 : ZMod 11692148857)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2617, 1), (186157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2617, 1), (186157, 1)] : List FactorBlock).map factorBlockValue).prod) = 11692148857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_2617
      · exact prime_oneHundredThirteenDG_186157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 11692148857) ^ 5846074428 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (15 : ZMod 11692148857) ^ 3897382952 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (15 : ZMod 11692148857) ^ 4467768 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (15 : ZMod 11692148857) ^ 62808 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_11712584857 : Nat.Prime 11712584857 := by
  apply lucas_primality 11712584857 (5 : ZMod 11712584857)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (3019, 1), (3299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (3019, 1), (3299, 1)] : List FactorBlock).map factorBlockValue).prod) = 11712584857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_3019
      · exact prime_oneHundredThirteenDG_3299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11712584857) ^ 5856292428 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 11712584857) ^ 3904194952 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 11712584857) ^ 1673226408 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 11712584857) ^ 3879624 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 11712584857) ^ 3550344 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_12448711741 : Nat.Prime 12448711741 := by
  apply lucas_primality 12448711741 (2 : ZMod 12448711741)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (239, 1), (868111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (239, 1), (868111, 1)] : List FactorBlock).map factorBlockValue).prod) = 12448711741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_239
      · exact prime_oneHundredThirteenDG_868111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12448711741) ^ 6224355870 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12448711741) ^ 4149570580 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12448711741) ^ 2489742348 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12448711741) ^ 52086660 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12448711741) ^ 14340 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_12590893201 : Nat.Prime 12590893201 := by
  apply lucas_primality 12590893201 (11 : ZMod 12590893201)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (10492411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (10492411, 1)] : List FactorBlock).map factorBlockValue).prod) = 12590893201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_10492411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 12590893201) ^ 6295446600 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 12590893201) ^ 4196964400 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 12590893201) ^ 2518178640 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 12590893201) ^ 1200 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_13152403867 : Nat.Prime 13152403867 := by
  apply lucas_primality 13152403867 (3 : ZMod 13152403867)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (313152473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (313152473, 1)] : List FactorBlock).map factorBlockValue).prod) = 13152403867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_313152473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13152403867) ^ 6576201933 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13152403867) ^ 4384134622 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13152403867) ^ 1878914838 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13152403867) ^ 42 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_16431195871 : Nat.Prime 16431195871 := by
  apply lucas_primality 16431195871 (21 : ZMod 16431195871)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (1721, 1), (3929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (1721, 1), (3929, 1)] : List FactorBlock).map factorBlockValue).prod) = 16431195871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_1721
      · exact prime_oneHundredThirteenDG_3929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 16431195871) ^ 8215597935 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (21 : ZMod 16431195871) ^ 5477065290 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (21 : ZMod 16431195871) ^ 3286239174 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (21 : ZMod 16431195871) ^ 9547470 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (21 : ZMod 16431195871) ^ 4182030 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_17583909073 : Nat.Prime 17583909073 := by
  apply lucas_primality 17583909073 (7 : ZMod 17583909073)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (366331439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (366331439, 1)] : List FactorBlock).map factorBlockValue).prod) = 17583909073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_366331439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 17583909073) ^ 8791954536 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 17583909073) ^ 5861303024 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 17583909073) ^ 48 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_17908439767 : Nat.Prime 17908439767 := by
  apply lucas_primality 17908439767 (5 : ZMod 17908439767)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (71, 1), (547, 1), (10979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (71, 1), (547, 1), (10979, 1)] : List FactorBlock).map factorBlockValue).prod) = 17908439767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_71
      · exact prime_oneHundredThirteenDG_547
      · exact prime_oneHundredThirteenDG_10979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 17908439767) ^ 8954219883 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 17908439767) ^ 5969479922 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 17908439767) ^ 2558348538 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 17908439767) ^ 252231546 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 17908439767) ^ 32739378 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 17908439767) ^ 1631154 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_19375107163 : Nat.Prime 19375107163 := by
  apply lucas_primality 19375107163 (2 : ZMod 19375107163)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (251, 1), (523, 1), (1447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (251, 1), (523, 1), (1447, 1)] : List FactorBlock).map factorBlockValue).prod) = 19375107163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_251
      · exact prime_oneHundredThirteenDG_523
      · exact prime_oneHundredThirteenDG_1447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19375107163) ^ 9687553581 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19375107163) ^ 6458369054 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19375107163) ^ 1139712186 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19375107163) ^ 77191662 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19375107163) ^ 37046094 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19375107163) ^ 13389846 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_29961219361 : Nat.Prime 29961219361 := by
  apply lucas_primality 29961219361 (7 : ZMod 29961219361)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (62419207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (62419207, 1)] : List FactorBlock).map factorBlockValue).prod) = 29961219361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_62419207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 29961219361) ^ 14980609680 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 29961219361) ^ 9987073120 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 29961219361) ^ 5992243872 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 29961219361) ^ 480 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_32177303971 : Nat.Prime 32177303971 := by
  apply lucas_primality 32177303971 (7 : ZMod 32177303971)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (10039, 1), (15263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (10039, 1), (15263, 1)] : List FactorBlock).map factorBlockValue).prod) = 32177303971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_10039
      · exact prime_oneHundredThirteenDG_15263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 32177303971) ^ 16088651985 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 32177303971) ^ 10725767990 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 32177303971) ^ 6435460794 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 32177303971) ^ 4596757710 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 32177303971) ^ 3205230 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 32177303971) ^ 2108190 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_33688104743 : Nat.Prime 33688104743 := by
  apply lucas_primality 33688104743 (5 : ZMod 33688104743)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (883, 1), (405871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (883, 1), (405871, 1)] : List FactorBlock).map factorBlockValue).prod) = 33688104743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_47
      · exact prime_oneHundredThirteenDG_883
      · exact prime_oneHundredThirteenDG_405871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33688104743) ^ 16844052371 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 33688104743) ^ 716768186 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 33688104743) ^ 38151874 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 33688104743) ^ 83002 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_38408045677 : Nat.Prime 38408045677 := by
  apply lucas_primality 38408045677 (5 : ZMod 38408045677)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (13, 1), (73, 1), (43801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (13, 1), (73, 1), (43801, 1)] : List FactorBlock).map factorBlockValue).prod) = 38408045677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_73
      · exact prime_oneHundredThirteenDG_43801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 38408045677) ^ 19204022838 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 38408045677) ^ 12802681892 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 38408045677) ^ 5486863668 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 38408045677) ^ 3491640516 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 38408045677) ^ 2954465052 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 38408045677) ^ 526137612 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 38408045677) ^ 876876 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_39332249497 : Nat.Prime 39332249497 := by
  apply lucas_primality 39332249497 (10 : ZMod 39332249497)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (546281243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (546281243, 1)] : List FactorBlock).map factorBlockValue).prod) = 39332249497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_546281243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 39332249497) ^ 19666124748 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 39332249497) ^ 13110749832 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 39332249497) ^ 72 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_40702291163 : Nat.Prime 40702291163 := by
  apply lucas_primality 40702291163 (2 : ZMod 40702291163)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1565472737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1565472737, 1)] : List FactorBlock).map factorBlockValue).prod) = 40702291163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_1565472737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 40702291163) ^ 20351145581 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 40702291163) ^ 3130945474 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 40702291163) ^ 26 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_50436610501 : Nat.Prime 50436610501 := by
  apply lucas_primality 50436610501 (2 : ZMod 50436610501)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (853, 1), (39419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (853, 1), (39419, 1)] : List FactorBlock).map factorBlockValue).prod) = 50436610501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_853
      · exact prime_oneHundredThirteenDG_39419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50436610501) ^ 25218305250 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 50436610501) ^ 16812203500 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 50436610501) ^ 10087322100 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 50436610501) ^ 59128500 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 50436610501) ^ 1279500 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_54583681961 : Nat.Prime 54583681961 := by
  apply lucas_primality 54583681961 (6 : ZMod 54583681961)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (1364592049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (1364592049, 1)] : List FactorBlock).map factorBlockValue).prod) = 54583681961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_1364592049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 54583681961) ^ 27291840980 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 54583681961) ^ 10916736392 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 54583681961) ^ 40 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_74017099073 : Nat.Prime 74017099073 := by
  apply lucas_primality 74017099073 (3 : ZMod 74017099073)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (73, 1), (2263243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (73, 1), (2263243, 1)] : List FactorBlock).map factorBlockValue).prod) = 74017099073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_73
      · exact prime_oneHundredThirteenDG_2263243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 74017099073) ^ 37008549536 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 74017099073) ^ 10573871296 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 74017099073) ^ 1013932864 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 74017099073) ^ 32704 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_75545359207 : Nat.Prime 75545359207 := by
  apply lucas_primality 75545359207 (6 : ZMod 75545359207)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12590893201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12590893201, 1)] : List FactorBlock).map factorBlockValue).prod) = 75545359207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_12590893201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 75545359207) ^ 37772679603 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 75545359207) ^ 25181786402 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 75545359207) ^ 6 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_85533645643 : Nat.Prime 85533645643 := by
  apply lucas_primality 85533645643 (2 : ZMod 85533645643)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (317, 1), (44970371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (317, 1), (44970371, 1)] : List FactorBlock).map factorBlockValue).prod) = 85533645643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_317
      · exact prime_oneHundredThirteenDG_44970371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 85533645643) ^ 42766822821 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 85533645643) ^ 28511215214 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 85533645643) ^ 269822226 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 85533645643) ^ 1902 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_100032476311 : Nat.Prime 100032476311 := by
  apply lucas_primality 100032476311 (3 : ZMod 100032476311)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (13, 1), (1229, 1), (23189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (13, 1), (1229, 1), (23189, 1)] : List FactorBlock).map factorBlockValue).prod) = 100032476311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_1229
      · exact prime_oneHundredThirteenDG_23189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 100032476311) ^ 50016238155 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 100032476311) ^ 33344158770 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 100032476311) ^ 20006495262 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 100032476311) ^ 7694805870 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 100032476311) ^ 81393390 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 100032476311) ^ 4313790 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_115686486229 : Nat.Prime 115686486229 := by
  apply lucas_primality 115686486229 (2 : ZMod 115686486229)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1279, 1), (7537561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1279, 1), (7537561, 1)] : List FactorBlock).map factorBlockValue).prod) = 115686486229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_1279
      · exact prime_oneHundredThirteenDG_7537561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 115686486229) ^ 57843243114 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 115686486229) ^ 38562162076 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 115686486229) ^ 90450732 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 115686486229) ^ 15348 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_116013785059 : Nat.Prime 116013785059 := by
  apply lucas_primality 116013785059 (2 : ZMod 116013785059)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (2148403427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (2148403427, 1)] : List FactorBlock).map factorBlockValue).prod) = 116013785059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_2148403427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116013785059) ^ 58006892529 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 116013785059) ^ 38671261686 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 116013785059) ^ 54 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_118033370017 : Nat.Prime 118033370017 := by
  apply lucas_primality 118033370017 (5 : ZMod 118033370017)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (1229514271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (1229514271, 1)] : List FactorBlock).map factorBlockValue).prod) = 118033370017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_1229514271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 118033370017) ^ 59016685008 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 118033370017) ^ 39344456672 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 118033370017) ^ 96 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_123907174841 : Nat.Prime 123907174841 := by
  apply lucas_primality 123907174841 (3 : ZMod 123907174841)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (31, 1), (103, 1), (970147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (31, 1), (103, 1), (970147, 1)] : List FactorBlock).map factorBlockValue).prod) = 123907174841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_31
      · exact prime_oneHundredThirteenDG_103
      · exact prime_oneHundredThirteenDG_970147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 123907174841) ^ 61953587420 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 123907174841) ^ 24781434968 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 123907174841) ^ 3997005640 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 123907174841) ^ 1202982280 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 123907174841) ^ 127720 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_139019920801 : Nat.Prime 139019920801 := by
  apply lucas_primality 139019920801 (7 : ZMod 139019920801)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 2), (17, 1), (3407351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 2), (17, 1), (3407351, 1)] : List FactorBlock).map factorBlockValue).prod) = 139019920801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_3407351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 139019920801) ^ 69509960400 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 139019920801) ^ 46339973600 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 139019920801) ^ 27803984160 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 139019920801) ^ 8177642400 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 139019920801) ^ 40800 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_141135171301 : Nat.Prime 141135171301 := by
  apply lucas_primality 141135171301 (2 : ZMod 141135171301)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (17, 1), (9224521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (17, 1), (9224521, 1)] : List FactorBlock).map factorBlockValue).prod) = 141135171301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_9224521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 141135171301) ^ 70567585650 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 141135171301) ^ 47045057100 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 141135171301) ^ 28227034260 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 141135171301) ^ 8302068900 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 141135171301) ^ 15300 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_147038650877 : Nat.Prime 147038650877 := by
  apply lucas_primality 147038650877 (2 : ZMod 147038650877)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (1087, 1), (2601349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (1087, 1), (2601349, 1)] : List FactorBlock).map factorBlockValue).prod) = 147038650877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_1087
      · exact prime_oneHundredThirteenDG_2601349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 147038650877) ^ 73519325438 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 147038650877) ^ 11310665452 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 147038650877) ^ 135270148 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 147038650877) ^ 56524 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_164311958711 : Nat.Prime 164311958711 := by
  apply lucas_primality 164311958711 (29 : ZMod 164311958711)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (16431195871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (16431195871, 1)] : List FactorBlock).map factorBlockValue).prod) = 164311958711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_16431195871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (29 : ZMod 164311958711) ^ 82155979355 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (29 : ZMod 164311958711) ^ 32862391742 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (29 : ZMod 164311958711) ^ 10 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_192458074477 : Nat.Prime 192458074477 := by
  apply lucas_primality 192458074477 (2 : ZMod 192458074477)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (499, 1), (32140627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (499, 1), (32140627, 1)] : List FactorBlock).map factorBlockValue).prod) = 192458074477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_499
      · exact prime_oneHundredThirteenDG_32140627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 192458074477) ^ 96229037238 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 192458074477) ^ 64152691492 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 192458074477) ^ 385687524 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 192458074477) ^ 5988 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_194055108703 : Nat.Prime 194055108703 := by
  apply lucas_primality 194055108703 (3 : ZMod 194055108703)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (67, 1), (5304661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (67, 1), (5304661, 1)] : List FactorBlock).map factorBlockValue).prod) = 194055108703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_67
      · exact prime_oneHundredThirteenDG_5304661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 194055108703) ^ 97027554351 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 194055108703) ^ 64685036234 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 194055108703) ^ 27722158386 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 194055108703) ^ 14927316054 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 194055108703) ^ 2896344906 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 194055108703) ^ 36582 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_210458679427 : Nat.Prime 210458679427 := by
  apply lucas_primality 210458679427 (2 : ZMod 210458679427)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11692148857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11692148857, 1)] : List FactorBlock).map factorBlockValue).prod) = 210458679427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_11692148857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 210458679427) ^ 105229339713 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 210458679427) ^ 70152893142 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 210458679427) ^ 18 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_235993496983 : Nat.Prime 235993496983 := by
  apply lucas_primality 235993496983 (3 : ZMod 235993496983)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (39332249497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (39332249497, 1)] : List FactorBlock).map factorBlockValue).prod) = 235993496983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_39332249497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 235993496983) ^ 117996748491 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 235993496983) ^ 78664498994 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 235993496983) ^ 6 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_255204401363 : Nat.Prime 255204401363 := by
  apply lucas_primality 255204401363 (2 : ZMod 255204401363)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (163, 1), (1607, 1), (25639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (163, 1), (1607, 1), (25639, 1)] : List FactorBlock).map factorBlockValue).prod) = 255204401363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_19
      · exact prime_oneHundredThirteenDG_163
      · exact prime_oneHundredThirteenDG_1607
      · exact prime_oneHundredThirteenDG_25639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 255204401363) ^ 127602200681 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 255204401363) ^ 13431810598 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 255204401363) ^ 1565671174 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 255204401363) ^ 158807966 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 255204401363) ^ 9953758 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_391079087023 : Nat.Prime 391079087023 := by
  apply lucas_primality 391079087023 (6 : ZMod 391079087023)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (1031, 1), (374083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (1031, 1), (374083, 1)] : List FactorBlock).map factorBlockValue).prod) = 391079087023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_1031
      · exact prime_oneHundredThirteenDG_374083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 391079087023) ^ 195539543511 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 391079087023) ^ 130359695674 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 391079087023) ^ 30083006694 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 391079087023) ^ 379320162 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 391079087023) ^ 1045434 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_656525954741 : Nat.Prime 656525954741 := by
  apply lucas_primality 656525954741 (2 : ZMod 656525954741)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2053, 1), (15989429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2053, 1), (15989429, 1)] : List FactorBlock).map factorBlockValue).prod) = 656525954741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_2053
      · exact prime_oneHundredThirteenDG_15989429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 656525954741) ^ 328262977370 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 656525954741) ^ 131305190948 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 656525954741) ^ 319788580 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 656525954741) ^ 41060 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_668735281349 : Nat.Prime 668735281349 := by
  apply lucas_primality 668735281349 (2 : ZMod 668735281349)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (52757, 1), (3168941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (52757, 1), (3168941, 1)] : List FactorBlock).map factorBlockValue).prod) = 668735281349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_52757
      · exact prime_oneHundredThirteenDG_3168941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 668735281349) ^ 334367640674 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 668735281349) ^ 12675764 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 668735281349) ^ 211028 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_745614003983 : Nat.Prime 745614003983 := by
  apply lucas_primality 745614003983 (5 : ZMod 745614003983)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (4188842719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (4188842719, 1)] : List FactorBlock).map factorBlockValue).prod) = 745614003983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_89
      · exact prime_oneHundredThirteenDG_4188842719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 745614003983) ^ 372807001991 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 745614003983) ^ 8377685438 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 745614003983) ^ 178 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_783309116561 : Nat.Prime 783309116561 := by
  apply lucas_primality 783309116561 (3 : ZMod 783309116561)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (9791363957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (9791363957, 1)] : List FactorBlock).map factorBlockValue).prod) = 783309116561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_9791363957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 783309116561) ^ 391654558280 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 783309116561) ^ 156661823312 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 783309116561) ^ 80 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_804194351021 : Nat.Prime 804194351021 := by
  apply lucas_primality 804194351021 (3 : ZMod 804194351021)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (37, 1), (2713, 1), (23563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (37, 1), (2713, 1), (23563, 1)] : List FactorBlock).map factorBlockValue).prod) = 804194351021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_37
      · exact prime_oneHundredThirteenDG_2713
      · exact prime_oneHundredThirteenDG_23563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 804194351021) ^ 402097175510 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 804194351021) ^ 160838870204 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 804194351021) ^ 47305550060 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 804194351021) ^ 21734982460 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 804194351021) ^ 296422540 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 804194351021) ^ 34129540 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_961348532161 : Nat.Prime 961348532161 := by
  apply lucas_primality 961348532161 (21 : ZMod 961348532161)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (23929, 1), (41849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (23929, 1), (41849, 1)] : List FactorBlock).map factorBlockValue).prod) = 961348532161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_23929
      · exact prime_oneHundredThirteenDG_41849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 961348532161) ^ 480674266080 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (21 : ZMod 961348532161) ^ 320449510720 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (21 : ZMod 961348532161) ^ 192269706432 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (21 : ZMod 961348532161) ^ 40175040 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (21 : ZMod 961348532161) ^ 22971840 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1081826648219 : Nat.Prime 1081826648219 := by
  apply lucas_primality 1081826648219 (2 : ZMod 1081826648219)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1213, 1), (10141, 1), (43973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1213, 1), (10141, 1), (43973, 1)] : List FactorBlock).map factorBlockValue).prod) = 1081826648219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_1213
      · exact prime_oneHundredThirteenDG_10141
      · exact prime_oneHundredThirteenDG_43973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1081826648219) ^ 540913324109 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081826648219) ^ 891860386 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081826648219) ^ 106678498 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081826648219) ^ 24602066 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1180333700171 : Nat.Prime 1180333700171 := by
  apply lucas_primality 1180333700171 (10 : ZMod 1180333700171)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (118033370017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (118033370017, 1)] : List FactorBlock).map factorBlockValue).prod) = 1180333700171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_118033370017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 1180333700171) ^ 590166850085 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1180333700171) ^ 236066740034 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1180333700171) ^ 10 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1627946835517 : Nat.Prime 1627946835517 := by
  apply lucas_primality 1627946835517 (2 : ZMod 1627946835517)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (30529, 1), (1481239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (30529, 1), (1481239, 1)] : List FactorBlock).map factorBlockValue).prod) = 1627946835517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_30529
      · exact prime_oneHundredThirteenDG_1481239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1627946835517) ^ 813973417758 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1627946835517) ^ 542648945172 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1627946835517) ^ 53324604 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1627946835517) ^ 1099044 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1879083925703 : Nat.Prime 1879083925703 := by
  apply lucas_primality 1879083925703 (5 : ZMod 1879083925703)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (37, 1), (5351, 1), (163637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (37, 1), (5351, 1), (163637, 1)] : List FactorBlock).map factorBlockValue).prod) = 1879083925703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_29
      · exact prime_oneHundredThirteenDG_37
      · exact prime_oneHundredThirteenDG_5351
      · exact prime_oneHundredThirteenDG_163637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1879083925703) ^ 939541962851 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1879083925703) ^ 64795997438 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1879083925703) ^ 50786052046 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1879083925703) ^ 351165002 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1879083925703) ^ 11483246 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1995777996703 : Nat.Prime 1995777996703 := by
  apply lucas_primality 1995777996703 (3 : ZMod 1995777996703)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (109, 1), (1033, 1), (60289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (109, 1), (1033, 1), (60289, 1)] : List FactorBlock).map factorBlockValue).prod) = 1995777996703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_109
      · exact prime_oneHundredThirteenDG_1033
      · exact prime_oneHundredThirteenDG_60289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1995777996703) ^ 997888998351 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1995777996703) ^ 665259332234 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1995777996703) ^ 285111142386 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1995777996703) ^ 18309889878 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1995777996703) ^ 1932021294 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1995777996703) ^ 33103518 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2114514524809 : Nat.Prime 2114514524809 := by
  apply lucas_primality 2114514524809 (13 : ZMod 2114514524809)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (18583, 1), (225769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (18583, 1), (225769, 1)] : List FactorBlock).map factorBlockValue).prod) = 2114514524809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_18583
      · exact prime_oneHundredThirteenDG_225769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2114514524809) ^ 1057257262404 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 2114514524809) ^ 704838174936 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 2114514524809) ^ 302073503544 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 2114514524809) ^ 113787576 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 2114514524809) ^ 9365832 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2115222571939 : Nat.Prime 2115222571939 := by
  apply lucas_primality 2115222571939 (3 : ZMod 2115222571939)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (397, 1), (607, 1), (208991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (397, 1), (607, 1), (208991, 1)] : List FactorBlock).map factorBlockValue).prod) = 2115222571939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_397
      · exact prime_oneHundredThirteenDG_607
      · exact prime_oneHundredThirteenDG_208991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2115222571939) ^ 1057611285969 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2115222571939) ^ 705074190646 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2115222571939) ^ 302174653134 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2115222571939) ^ 5328016554 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2115222571939) ^ 3484715934 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2115222571939) ^ 10121118 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2283405849691 : Nat.Prime 2283405849691 := by
  apply lucas_primality 2283405849691 (3 : ZMod 2283405849691)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (953, 1), (11409613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (953, 1), (11409613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2283405849691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_953
      · exact prime_oneHundredThirteenDG_11409613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2283405849691) ^ 1141702924845 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2283405849691) ^ 761135283230 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2283405849691) ^ 456681169938 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2283405849691) ^ 326200835670 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2283405849691) ^ 2396018730 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2283405849691) ^ 200130 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2823227978759 : Nat.Prime 2823227978759 := by
  apply lucas_primality 2823227978759 (11 : ZMod 2823227978759)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (140551, 1), (913039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (140551, 1), (913039, 1)] : List FactorBlock).map factorBlockValue).prod) = 2823227978759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_140551
      · exact prime_oneHundredThirteenDG_913039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2823227978759) ^ 1411613989379 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2823227978759) ^ 256657088978 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2823227978759) ^ 20086858 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2823227978759) ^ 3092122 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2954430198833 : Nat.Prime 2954430198833 := by
  apply lucas_primality 2954430198833 (3 : ZMod 2954430198833)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (17, 1), (29, 1), (53506777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (17, 1), (29, 1), (53506777, 1)] : List FactorBlock).map factorBlockValue).prod) = 2954430198833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_29
      · exact prime_oneHundredThirteenDG_53506777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2954430198833) ^ 1477215099416 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2954430198833) ^ 422061456976 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2954430198833) ^ 173790011696 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2954430198833) ^ 101876903408 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2954430198833) ^ 55216 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_3000974289331 : Nat.Prime 3000974289331 := by
  apply lucas_primality 3000974289331 (2 : ZMod 3000974289331)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (100032476311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (100032476311, 1)] : List FactorBlock).map factorBlockValue).prod) = 3000974289331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_100032476311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3000974289331) ^ 1500487144665 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3000974289331) ^ 1000324763110 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3000974289331) ^ 600194857866 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3000974289331) ^ 30 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_3248385981653 : Nat.Prime 3248385981653 := by
  apply lucas_primality 3248385981653 (3 : ZMod 3248385981653)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (116013785059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (116013785059, 1)] : List FactorBlock).map factorBlockValue).prod) = 3248385981653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_116013785059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3248385981653) ^ 1624192990826 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3248385981653) ^ 464055140236 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3248385981653) ^ 28 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_3282440935913 : Nat.Prime 3282440935913 := by
  apply lucas_primality 3282440935913 (3 : ZMod 3282440935913)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (349, 1), (3613, 1), (19141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (349, 1), (3613, 1), (19141, 1)] : List FactorBlock).map factorBlockValue).prod) = 3282440935913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_349
      · exact prime_oneHundredThirteenDG_3613
      · exact prime_oneHundredThirteenDG_19141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3282440935913) ^ 1641220467956 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3282440935913) ^ 193084760936 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3282440935913) ^ 9405274888 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3282440935913) ^ 908508424 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3282440935913) ^ 171487432 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_3882857796457 : Nat.Prime 3882857796457 := by
  apply lucas_primality 3882857796457 (5 : ZMod 3882857796457)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (6131, 1), (26388149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (6131, 1), (26388149, 1)] : List FactorBlock).map factorBlockValue).prod) = 3882857796457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_6131
      · exact prime_oneHundredThirteenDG_26388149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3882857796457) ^ 1941428898228 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3882857796457) ^ 1294285932152 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3882857796457) ^ 633315576 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3882857796457) ^ 147144 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_3973878919447 : Nat.Prime 3973878919447 := by
  apply lucas_primality 3973878919447 (3 : ZMod 3973878919447)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (71, 1), (863, 1), (292141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (71, 1), (863, 1), (292141, 1)] : List FactorBlock).map factorBlockValue).prod) = 3973878919447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_37
      · exact prime_oneHundredThirteenDG_71
      · exact prime_oneHundredThirteenDG_863
      · exact prime_oneHundredThirteenDG_292141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3973878919447) ^ 1986939459723 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3973878919447) ^ 1324626306482 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3973878919447) ^ 107402132958 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3973878919447) ^ 55970125626 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3973878919447) ^ 4604726442 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3973878919447) ^ 13602606 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_5501035010749 : Nat.Prime 5501035010749 := by
  apply lucas_primality 5501035010749 (6 : ZMod 5501035010749)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (11180965469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (11180965469, 1)] : List FactorBlock).map factorBlockValue).prod) = 5501035010749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_41
      · exact prime_oneHundredThirteenDG_11180965469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5501035010749) ^ 2750517505374 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 5501035010749) ^ 1833678336916 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 5501035010749) ^ 134171585628 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 5501035010749) ^ 492 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_5576148677923 : Nat.Prime 5576148677923 := by
  apply lucas_primality 5576148677923 (5 : ZMod 5576148677923)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (8685589841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (8685589841, 1)] : List FactorBlock).map factorBlockValue).prod) = 5576148677923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_107
      · exact prime_oneHundredThirteenDG_8685589841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5576148677923) ^ 2788074338961 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5576148677923) ^ 1858716225974 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5576148677923) ^ 52113539046 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5576148677923) ^ 642 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_5842647745397 : Nat.Prime 5842647745397 := by
  apply lucas_primality 5842647745397 (3 : ZMod 5842647745397)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (31, 1), (7559, 1), (80953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (31, 1), (7559, 1), (80953, 1)] : List FactorBlock).map factorBlockValue).prod) = 5842647745397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_31
      · exact prime_oneHundredThirteenDG_7559
      · exact prime_oneHundredThirteenDG_80953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5842647745397) ^ 2921323872698 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5842647745397) ^ 834663963628 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5842647745397) ^ 531149795036 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5842647745397) ^ 188472507916 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5842647745397) ^ 772939244 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5842647745397) ^ 72173332 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_6564881871827 : Nat.Prime 6564881871827 := by
  apply lucas_primality 6564881871827 (2 : ZMod 6564881871827)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3282440935913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3282440935913, 1)] : List FactorBlock).map factorBlockValue).prod) = 6564881871827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3282440935913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 6564881871827) ^ 3282440935913 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6564881871827) ^ 2 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_7057838785549 : Nat.Prime 7057838785549 := by
  apply lucas_primality 7057838785549 (2 : ZMod 7057838785549)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4519, 1), (130151191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4519, 1), (130151191, 1)] : List FactorBlock).map factorBlockValue).prod) = 7057838785549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_4519
      · exact prime_oneHundredThirteenDG_130151191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7057838785549) ^ 3528919392774 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7057838785549) ^ 2352612928516 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7057838785549) ^ 1561814292 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7057838785549) ^ 54228 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_8390409146263 : Nat.Prime 8390409146263 := by
  apply lucas_primality 8390409146263 (3 : ZMod 8390409146263)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (11, 1), (13, 2), (113, 1), (373, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (11, 1), (13, 2), (113, 1), (373, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) = 8390409146263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_113
      · exact prime_oneHundredThirteenDG_373
      · exact prime_oneHundredThirteenDG_661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8390409146263) ^ 4195204573131 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8390409146263) ^ 2796803048754 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8390409146263) ^ 762764467842 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8390409146263) ^ 645416088174 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8390409146263) ^ 74251408374 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8390409146263) ^ 22494394494 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8390409146263) ^ 12693508542 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_9600814353859 : Nat.Prime 9600814353859 := by
  apply lucas_primality 9600814353859 (3 : ZMod 9600814353859)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (17583909073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (17583909073, 1)] : List FactorBlock).map factorBlockValue).prod) = 9600814353859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_17583909073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9600814353859) ^ 4800407176929 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9600814353859) ^ 3200271451286 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9600814353859) ^ 1371544907694 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9600814353859) ^ 738524181066 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9600814353859) ^ 546 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_9619159692313 : Nat.Prime 9619159692313 := by
  apply lucas_primality 9619159692313 (5 : ZMod 9619159692313)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (41, 1), (3258522931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (41, 1), (3258522931, 1)] : List FactorBlock).map factorBlockValue).prod) = 9619159692313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_41
      · exact prime_oneHundredThirteenDG_3258522931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9619159692313) ^ 4809579846156 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 9619159692313) ^ 3206386564104 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 9619159692313) ^ 234613651032 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 9619159692313) ^ 2952 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_13439076342389 : Nat.Prime 13439076342389 := by
  apply lucas_primality 13439076342389 (2 : ZMod 13439076342389)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (258659, 1), (351059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (258659, 1), (351059, 1)] : List FactorBlock).map factorBlockValue).prod) = 13439076342389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_37
      · exact prime_oneHundredThirteenDG_258659
      · exact prime_oneHundredThirteenDG_351059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13439076342389) ^ 6719538171194 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 13439076342389) ^ 363218279524 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 13439076342389) ^ 51956732 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 13439076342389) ^ 38281532 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_14273589247651 : Nat.Prime 14273589247651 := by
  apply lucas_primality 14273589247651 (2 : ZMod 14273589247651)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (19, 1), (379, 1), (4404817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (19, 1), (379, 1), (4404817, 1)] : List FactorBlock).map factorBlockValue).prod) = 14273589247651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_19
      · exact prime_oneHundredThirteenDG_379
      · exact prime_oneHundredThirteenDG_4404817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14273589247651) ^ 7136794623825 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14273589247651) ^ 4757863082550 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14273589247651) ^ 2854717849530 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14273589247651) ^ 751241539350 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14273589247651) ^ 37661185350 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14273589247651) ^ 3240450 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_15703918998743 : Nat.Prime 15703918998743 := by
  apply lucas_primality 15703918998743 (5 : ZMod 15703918998743)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (9479, 1), (63719473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (9479, 1), (63719473, 1)] : List FactorBlock).map factorBlockValue).prod) = 15703918998743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_9479
      · exact prime_oneHundredThirteenDG_63719473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15703918998743) ^ 7851959499371 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 15703918998743) ^ 1207993769134 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 15703918998743) ^ 1656706298 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 15703918998743) ^ 246454 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_28756249808861 : Nat.Prime 28756249808861 := by
  apply lucas_primality 28756249808861 (14 : ZMod 28756249808861)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (23, 1), (37, 1), (241365199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (23, 1), (37, 1), (241365199, 1)] : List FactorBlock).map factorBlockValue).prod) = 28756249808861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_23
      · exact prime_oneHundredThirteenDG_37
      · exact prime_oneHundredThirteenDG_241365199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 28756249808861) ^ 14378124904430 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (14 : ZMod 28756249808861) ^ 5751249961772 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (14 : ZMod 28756249808861) ^ 4108035686980 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (14 : ZMod 28756249808861) ^ 1250271730820 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (14 : ZMod 28756249808861) ^ 777195940780 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (14 : ZMod 28756249808861) ^ 119140 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_30294064138579 : Nat.Prime 30294064138579 := by
  apply lucas_primality 30294064138579 (10 : ZMod 30294064138579)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (9421, 1), (17288113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (9421, 1), (17288113, 1)] : List FactorBlock).map factorBlockValue).prod) = 30294064138579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_31
      · exact prime_oneHundredThirteenDG_9421
      · exact prime_oneHundredThirteenDG_17288113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 30294064138579) ^ 15147032069289 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 30294064138579) ^ 10098021379526 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 30294064138579) ^ 977227875438 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 30294064138579) ^ 3215589018 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 30294064138579) ^ 1752306 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_31813925961647 : Nat.Prime 31813925961647 := by
  apply lucas_primality 31813925961647 (5 : ZMod 31813925961647)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (821, 1), (19375107163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (821, 1), (19375107163, 1)] : List FactorBlock).map factorBlockValue).prod) = 31813925961647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_821
      · exact prime_oneHundredThirteenDG_19375107163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 31813925961647) ^ 15906962980823 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 31813925961647) ^ 38750214326 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 31813925961647) ^ 1642 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_32928147032161 : Nat.Prime 32928147032161 := by
  apply lucas_primality 32928147032161 (7 : ZMod 32928147032161)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (31, 1), (2212913107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (31, 1), (2212913107, 1)] : List FactorBlock).map factorBlockValue).prod) = 32928147032161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_31
      · exact prime_oneHundredThirteenDG_2212913107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 32928147032161) ^ 16464073516080 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 32928147032161) ^ 10976049010720 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 32928147032161) ^ 6585629406432 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 32928147032161) ^ 1062198291360 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 32928147032161) ^ 14880 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_33561636585053 : Nat.Prime 33561636585053 := by
  apply lucas_primality 33561636585053 (2 : ZMod 33561636585053)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8390409146263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8390409146263, 1)] : List FactorBlock).map factorBlockValue).prod) = 33561636585053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_8390409146263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 33561636585053) ^ 16780818292526 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 33561636585053) ^ 4 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_45453621948629 : Nat.Prime 45453621948629 := by
  apply lucas_primality 45453621948629 (2 : ZMod 45453621948629)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (431, 1), (4231, 1), (6231437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (431, 1), (4231, 1), (6231437, 1)] : List FactorBlock).map factorBlockValue).prod) = 45453621948629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_431
      · exact prime_oneHundredThirteenDG_4231
      · exact prime_oneHundredThirteenDG_6231437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45453621948629) ^ 22726810974314 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 45453621948629) ^ 105460839788 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 45453621948629) ^ 10742997388 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 45453621948629) ^ 7294244 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_46695030271313 : Nat.Prime 46695030271313 := by
  apply lucas_primality 46695030271313 (3 : ZMod 46695030271313)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (521, 1), (69119, 1), (81043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (521, 1), (69119, 1), (81043, 1)] : List FactorBlock).map factorBlockValue).prod) = 46695030271313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_521
      · exact prime_oneHundredThirteenDG_69119
      · exact prime_oneHundredThirteenDG_81043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 46695030271313) ^ 23347515135656 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 46695030271313) ^ 89625777872 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 46695030271313) ^ 675574448 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 46695030271313) ^ 576175984 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_48015588629297 : Nat.Prime 48015588629297 := by
  apply lucas_primality 48015588629297 (3 : ZMod 48015588629297)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3000974289331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3000974289331, 1)] : List FactorBlock).map factorBlockValue).prod) = 48015588629297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3000974289331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 48015588629297) ^ 24007794314648 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 48015588629297) ^ 16 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_71553534474133 : Nat.Prime 71553534474133 := by
  apply lucas_primality 71553534474133 (5 : ZMod 71553534474133)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (59, 1), (33688104743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (59, 1), (33688104743, 1)] : List FactorBlock).map factorBlockValue).prod) = 71553534474133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_59
      · exact prime_oneHundredThirteenDG_33688104743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 71553534474133) ^ 35776767237066 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 71553534474133) ^ 23851178158044 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 71553534474133) ^ 1212771770748 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 71553534474133) ^ 2124 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_124935112703561 : Nat.Prime 124935112703561 := by
  apply lucas_primality 124935112703561 (6 : ZMod 124935112703561)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (17, 2), (67, 1), (161306503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (17, 2), (67, 1), (161306503, 1)] : List FactorBlock).map factorBlockValue).prod) = 124935112703561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_67
      · exact prime_oneHundredThirteenDG_161306503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 124935112703561) ^ 62467556351780 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 124935112703561) ^ 24987022540712 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 124935112703561) ^ 7349124276680 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 124935112703561) ^ 1864703174680 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 124935112703561) ^ 774520 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_147626805480509 : Nat.Prime 147626805480509 := by
  apply lucas_primality 147626805480509 (2 : ZMod 147626805480509)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (251, 1), (147038650877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (251, 1), (147038650877, 1)] : List FactorBlock).map factorBlockValue).prod) = 147626805480509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_251
      · exact prime_oneHundredThirteenDG_147038650877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 147626805480509) ^ 73813402740254 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 147626805480509) ^ 588154603508 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 147626805480509) ^ 1004 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_173080514215789 : Nat.Prime 173080514215789 := by
  apply lucas_primality 173080514215789 (6 : ZMod 173080514215789)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37951, 1), (380052599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37951, 1), (380052599, 1)] : List FactorBlock).map factorBlockValue).prod) = 173080514215789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_37951
      · exact prime_oneHundredThirteenDG_380052599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 173080514215789) ^ 86540257107894 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 173080514215789) ^ 57693504738596 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 173080514215789) ^ 4560631188 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 173080514215789) ^ 455412 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_180743154582101 : Nat.Prime 180743154582101 := by
  apply lucas_primality 180743154582101 (2 : ZMod 180743154582101)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (164311958711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (164311958711, 1)] : List FactorBlock).map factorBlockValue).prod) = 180743154582101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_164311958711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 180743154582101) ^ 90371577291050 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 180743154582101) ^ 36148630916420 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 180743154582101) ^ 16431195871100 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 180743154582101) ^ 1100 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_228613561254373 : Nat.Prime 228613561254373 := by
  apply lucas_primality 228613561254373 (2 : ZMod 228613561254373)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (61, 1), (72383, 1), (616391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (61, 1), (72383, 1), (616391, 1)] : List FactorBlock).map factorBlockValue).prod) = 228613561254373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_61
      · exact prime_oneHundredThirteenDG_72383
      · exact prime_oneHundredThirteenDG_616391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 228613561254373) ^ 114306780627186 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 228613561254373) ^ 76204520418124 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 228613561254373) ^ 32659080179196 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 228613561254373) ^ 3747763299252 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 228613561254373) ^ 3158387484 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 228613561254373) ^ 370890492 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_295253610961019 : Nat.Prime 295253610961019 := by
  apply lucas_primality 295253610961019 (2 : ZMod 295253610961019)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (147626805480509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (147626805480509, 1)] : List FactorBlock).map factorBlockValue).prod) = 295253610961019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_147626805480509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 295253610961019) ^ 147626805480509 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 295253610961019) ^ 2 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_371812832011493 : Nat.Prime 371812832011493 := by
  apply lucas_primality 371812832011493 (2 : ZMod 371812832011493)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 1), (193871, 1), (4398707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 1), (193871, 1), (4398707, 1)] : List FactorBlock).map factorBlockValue).prod) = 371812832011493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_109
      · exact prime_oneHundredThirteenDG_193871
      · exact prime_oneHundredThirteenDG_4398707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 371812832011493) ^ 185906416005746 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 371812832011493) ^ 3411126899188 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 371812832011493) ^ 1917836252 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 371812832011493) ^ 84527756 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_420865080819583 : Nat.Prime 420865080819583 := by
  apply lucas_primality 420865080819583 (5 : ZMod 420865080819583)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (71, 1), (141135171301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (71, 1), (141135171301, 1)] : List FactorBlock).map factorBlockValue).prod) = 420865080819583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_71
      · exact prime_oneHundredThirteenDG_141135171301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 420865080819583) ^ 210432540409791 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 420865080819583) ^ 140288360273194 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 420865080819583) ^ 60123582974226 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 420865080819583) ^ 5927677194642 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 420865080819583) ^ 2982 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_574679810388323 : Nat.Prime 574679810388323 := by
  apply lucas_primality 574679810388323 (2 : ZMod 574679810388323)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1493, 1), (192458074477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1493, 1), (192458074477, 1)] : List FactorBlock).map factorBlockValue).prod) = 574679810388323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_1493
      · exact prime_oneHundredThirteenDG_192458074477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 574679810388323) ^ 287339905194161 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 574679810388323) ^ 384916148954 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 574679810388323) ^ 2986 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_598549087537103 : Nat.Prime 598549087537103 := by
  apply lucas_primality 598549087537103 (5 : ZMod 598549087537103)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (31, 1), (53, 1), (283, 1), (49511083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (31, 1), (53, 1), (283, 1), (49511083, 1)] : List FactorBlock).map factorBlockValue).prod) = 598549087537103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_31
      · exact prime_oneHundredThirteenDG_53
      · exact prime_oneHundredThirteenDG_283
      · exact prime_oneHundredThirteenDG_49511083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 598549087537103) ^ 299274543768551 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 598549087537103) ^ 46042237502854 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 598549087537103) ^ 19308035081842 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 598549087537103) ^ 11293379010134 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 598549087537103) ^ 2115014443594 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 598549087537103) ^ 12089194 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_871490090456569 : Nat.Prime 871490090456569 := by
  apply lucas_primality 871490090456569 (7 : ZMod 871490090456569)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (120503, 1), (9131443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (120503, 1), (9131443, 1)] : List FactorBlock).map factorBlockValue).prod) = 871490090456569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_120503
      · exact prime_oneHundredThirteenDG_9131443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 871490090456569) ^ 435745045228284 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 871490090456569) ^ 290496696818856 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 871490090456569) ^ 79226371859688 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 871490090456569) ^ 7232102856 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 871490090456569) ^ 95438376 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1059084928985383 : Nat.Prime 1059084928985383 := by
  apply lucas_primality 1059084928985383 (3 : ZMod 1059084928985383)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (47, 1), (1019, 1), (94502411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (47, 1), (1019, 1), (94502411, 1)] : List FactorBlock).map factorBlockValue).prod) = 1059084928985383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_47
      · exact prime_oneHundredThirteenDG_1019
      · exact prime_oneHundredThirteenDG_94502411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1059084928985383) ^ 529542464492691 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1059084928985383) ^ 353028309661794 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1059084928985383) ^ 81468071460414 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1059084928985383) ^ 22533721893306 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1059084928985383) ^ 1039337516178 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1059084928985383) ^ 11206962 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1911480966208871 : Nat.Prime 1911480966208871 := by
  apply lucas_primality 1911480966208871 (7 : ZMod 1911480966208871)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (107, 1), (255204401363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (107, 1), (255204401363, 1)] : List FactorBlock).map factorBlockValue).prod) = 1911480966208871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_107
      · exact prime_oneHundredThirteenDG_255204401363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1911480966208871) ^ 955740483104435 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1911480966208871) ^ 382296193241774 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1911480966208871) ^ 273068709458410 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1911480966208871) ^ 17864308095410 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1911480966208871) ^ 7490 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1990310537524819 : Nat.Prime 1990310537524819 := by
  apply lucas_primality 1990310537524819 (14 : ZMod 1990310537524819)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (7057838785549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (7057838785549, 1)] : List FactorBlock).map factorBlockValue).prod) = 1990310537524819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_47
      · exact prime_oneHundredThirteenDG_7057838785549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 1990310537524819) ^ 995155268762409 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (14 : ZMod 1990310537524819) ^ 663436845841606 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (14 : ZMod 1990310537524819) ^ 42347032713294 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (14 : ZMod 1990310537524819) ^ 282 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2332082163085397 : Nat.Prime 2332082163085397 := by
  apply lucas_primality 2332082163085397 (2 : ZMod 2332082163085397)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (330133, 1), (1766017153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (330133, 1), (1766017153, 1)] : List FactorBlock).map factorBlockValue).prod) = 2332082163085397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_330133
      · exact prime_oneHundredThirteenDG_1766017153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2332082163085397) ^ 1166041081542698 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2332082163085397) ^ 7064068612 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2332082163085397) ^ 1320532 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2432820172120523 : Nat.Prime 2432820172120523 := by
  apply lucas_primality 2432820172120523 (2 : ZMod 2432820172120523)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (71553534474133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (71553534474133, 1)] : List FactorBlock).map factorBlockValue).prod) = 2432820172120523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_71553534474133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2432820172120523) ^ 1216410086060261 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2432820172120523) ^ 143107068948266 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2432820172120523) ^ 34 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2484818577636503 : Nat.Prime 2484818577636503 := by
  apply lucas_primality 2484818577636503 (5 : ZMod 2484818577636503)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2411, 1), (4127, 1), (124862783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2411, 1), (4127, 1), (124862783, 1)] : List FactorBlock).map factorBlockValue).prod) = 2484818577636503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_2411
      · exact prime_oneHundredThirteenDG_4127
      · exact prime_oneHundredThirteenDG_124862783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2484818577636503) ^ 1242409288818251 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2484818577636503) ^ 1030617410882 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2484818577636503) ^ 602088339626 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2484818577636503) ^ 19900394 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_4072182523090817 : Nat.Prime 4072182523090817 := by
  apply lucas_primality 4072182523090817 (3 : ZMod 4072182523090817)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (31813925961647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (31813925961647, 1)] : List FactorBlock).map factorBlockValue).prod) = 4072182523090817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_31813925961647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 4072182523090817) ^ 2036091261545408 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4072182523090817) ^ 128 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_4511502615449569 : Nat.Prime 4511502615449569 := by
  apply lucas_primality 4511502615449569 (14 : ZMod 4511502615449569)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (1109, 1), (23599, 1), (1795663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (1109, 1), (23599, 1), (1795663, 1)] : List FactorBlock).map factorBlockValue).prod) = 4511502615449569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_1109
      · exact prime_oneHundredThirteenDG_23599
      · exact prime_oneHundredThirteenDG_1795663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 4511502615449569) ^ 2255751307724784 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (14 : ZMod 4511502615449569) ^ 1503834205149856 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (14 : ZMod 4511502615449569) ^ 4068081709152 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (14 : ZMod 4511502615449569) ^ 191173465632 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (14 : ZMod 4511502615449569) ^ 2512443936 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_5087238247737011 : Nat.Prime 5087238247737011 := by
  apply lucas_primality 5087238247737011 (2 : ZMod 5087238247737011)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (431, 1), (1180333700171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (431, 1), (1180333700171, 1)] : List FactorBlock).map factorBlockValue).prod) = 5087238247737011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_431
      · exact prime_oneHundredThirteenDG_1180333700171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5087238247737011) ^ 2543619123868505 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5087238247737011) ^ 1017447649547402 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5087238247737011) ^ 11803337001710 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5087238247737011) ^ 4310 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_6330465756109267 : Nat.Prime 6330465756109267 := by
  apply lucas_primality 6330465756109267 (2 : ZMod 6330465756109267)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5437, 1), (194055108703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5437, 1), (194055108703, 1)] : List FactorBlock).map factorBlockValue).prod) = 6330465756109267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5437
      · exact prime_oneHundredThirteenDG_194055108703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6330465756109267) ^ 3165232878054633 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6330465756109267) ^ 2110155252036422 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6330465756109267) ^ 1164330652218 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6330465756109267) ^ 32622 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_7425089584136171 : Nat.Prime 7425089584136171 := by
  apply lucas_primality 7425089584136171 (2 : ZMod 7425089584136171)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (263, 1), (2823227978759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (263, 1), (2823227978759, 1)] : List FactorBlock).map factorBlockValue).prod) = 7425089584136171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_263
      · exact prime_oneHundredThirteenDG_2823227978759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7425089584136171) ^ 3712544792068085 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7425089584136171) ^ 1485017916827234 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7425089584136171) ^ 28232279787590 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7425089584136171) ^ 2630 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_8014846112349101 : Nat.Prime 8014846112349101 := by
  apply lucas_primality 8014846112349101 (2 : ZMod 8014846112349101)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (283, 1), (6101, 1), (46420277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (283, 1), (6101, 1), (46420277, 1)] : List FactorBlock).map factorBlockValue).prod) = 8014846112349101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_283
      · exact prime_oneHundredThirteenDG_6101
      · exact prime_oneHundredThirteenDG_46420277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8014846112349101) ^ 4007423056174550 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8014846112349101) ^ 1602969222469820 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8014846112349101) ^ 28321010997700 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8014846112349101) ^ 1313693839100 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8014846112349101) ^ 172658300 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_8227825144249133 : Nat.Prime 8227825144249133 := by
  apply lucas_primality 8227825144249133 (2 : ZMod 8227825144249133)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (2399, 1), (50436610501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (2399, 1), (50436610501, 1)] : List FactorBlock).map factorBlockValue).prod) = 8227825144249133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_2399
      · exact prime_oneHundredThirteenDG_50436610501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8227825144249133) ^ 4113912572124566 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8227825144249133) ^ 483989714367596 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8227825144249133) ^ 3429689514068 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8227825144249133) ^ 163132 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_8507185875978631 : Nat.Prime 8507185875978631 := by
  apply lucas_primality 8507185875978631 (3 : ZMod 8507185875978631)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (6967, 1), (40702291163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (6967, 1), (40702291163, 1)] : List FactorBlock).map factorBlockValue).prod) = 8507185875978631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_6967
      · exact prime_oneHundredThirteenDG_40702291163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8507185875978631) ^ 4253592937989315 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8507185875978631) ^ 2835728625326210 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8507185875978631) ^ 1701437175195726 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8507185875978631) ^ 1221068734890 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8507185875978631) ^ 209010 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_9559578382337813 : Nat.Prime 9559578382337813 := by
  apply lucas_primality 9559578382337813 (2 : ZMod 9559578382337813)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (257, 1), (141907, 1), (65530247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (257, 1), (141907, 1), (65530247, 1)] : List FactorBlock).map factorBlockValue).prod) = 9559578382337813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_257
      · exact prime_oneHundredThirteenDG_141907
      · exact prime_oneHundredThirteenDG_65530247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9559578382337813) ^ 4779789191168906 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9559578382337813) ^ 37196803044116 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9559578382337813) ^ 67365093916 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9559578382337813) ^ 145880396 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_10174476495474023 : Nat.Prime 10174476495474023 := by
  apply lucas_primality 10174476495474023 (5 : ZMod 10174476495474023)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5087238247737011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5087238247737011, 1)] : List FactorBlock).map factorBlockValue).prod) = 10174476495474023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5087238247737011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 10174476495474023) ^ 5087238247737011 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 10174476495474023) ^ 2 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_11443621107531271 : Nat.Prime 11443621107531271 := by
  apply lucas_primality 11443621107531271 (6 : ZMod 11443621107531271)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (29, 1), (1879083925703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (29, 1), (1879083925703, 1)] : List FactorBlock).map factorBlockValue).prod) = 11443621107531271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_29
      · exact prime_oneHundredThirteenDG_1879083925703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 11443621107531271) ^ 5721810553765635 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 11443621107531271) ^ 3814540369177090 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 11443621107531271) ^ 2288724221506254 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 11443621107531271) ^ 1634803015361610 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 11443621107531271) ^ 394607624397630 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 11443621107531271) ^ 6090 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_12104727555536969 : Nat.Prime 12104727555536969 := by
  apply lucas_primality 12104727555536969 (3 : ZMod 12104727555536969)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (29, 1), (773, 1), (5209, 1), (1177987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (29, 1), (773, 1), (5209, 1), (1177987, 1)] : List FactorBlock).map factorBlockValue).prod) = 12104727555536969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_29
      · exact prime_oneHundredThirteenDG_773
      · exact prime_oneHundredThirteenDG_5209
      · exact prime_oneHundredThirteenDG_1177987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12104727555536969) ^ 6052363777768484 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12104727555536969) ^ 1100429777776088 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12104727555536969) ^ 417404398466792 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12104727555536969) ^ 15659414690216 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12104727555536969) ^ 2323810242952 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12104727555536969) ^ 10275773464 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_12636106901718863 : Nat.Prime 12636106901718863 := by
  apply lucas_primality 12636106901718863 (5 : ZMod 12636106901718863)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (45453621948629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (45453621948629, 1)] : List FactorBlock).map factorBlockValue).prod) = 12636106901718863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_139
      · exact prime_oneHundredThirteenDG_45453621948629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 12636106901718863) ^ 6318053450859431 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 12636106901718863) ^ 90907243897258 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 12636106901718863) ^ 278 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_12757984316450873 : Nat.Prime 12757984316450873 := by
  apply lucas_primality 12757984316450873 (3 : ZMod 12757984316450873)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (317, 1), (4133, 1), (28307333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (317, 1), (4133, 1), (28307333, 1)] : List FactorBlock).map factorBlockValue).prod) = 12757984316450873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_43
      · exact prime_oneHundredThirteenDG_317
      · exact prime_oneHundredThirteenDG_4133
      · exact prime_oneHundredThirteenDG_28307333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12757984316450873) ^ 6378992158225436 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12757984316450873) ^ 296697309684904 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12757984316450873) ^ 40246007307416 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12757984316450873) ^ 3086858048984 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12757984316450873) ^ 450695384 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_14212895049641593 : Nat.Prime 14212895049641593 := by
  apply lucas_primality 14212895049641593 (5 : ZMod 14212895049641593)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (71353, 1), (307393943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (71353, 1), (307393943, 1)] : List FactorBlock).map factorBlockValue).prod) = 14212895049641593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_71353
      · exact prime_oneHundredThirteenDG_307393943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14212895049641593) ^ 7106447524820796 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 14212895049641593) ^ 4737631683213864 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 14212895049641593) ^ 199191275064 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 14212895049641593) ^ 46236744 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_15588219408245191 : Nat.Prime 15588219408245191 := by
  apply lucas_primality 15588219408245191 (3 : ZMod 15588219408245191)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (37, 1), (668735281349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (37, 1), (668735281349, 1)] : List FactorBlock).map factorBlockValue).prod) = 15588219408245191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_37
      · exact prime_oneHundredThirteenDG_668735281349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15588219408245191) ^ 7794109704122595 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 15588219408245191) ^ 5196073136081730 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 15588219408245191) ^ 3117643881649038 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 15588219408245191) ^ 2226888486892170 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 15588219408245191) ^ 421303227249870 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 15588219408245191) ^ 23310 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_15717909905190737 : Nat.Prime 15717909905190737 := by
  apply lucas_primality 15717909905190737 (3 : ZMod 15717909905190737)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2377, 1), (9181, 1), (45014833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2377, 1), (9181, 1), (45014833, 1)] : List FactorBlock).map factorBlockValue).prod) = 15717909905190737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_2377
      · exact prime_oneHundredThirteenDG_9181
      · exact prime_oneHundredThirteenDG_45014833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 15717909905190737) ^ 7858954952595368 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 15717909905190737) ^ 6612498908368 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 15717909905190737) ^ 1712004128656 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 15717909905190737) ^ 349171792 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_19897316743356971 : Nat.Prime 19897316743356971 := by
  apply lucas_primality 19897316743356971 (2 : ZMod 19897316743356971)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1879, 1), (903757, 1), (1171699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1879, 1), (903757, 1), (1171699, 1)] : List FactorBlock).map factorBlockValue).prod) = 19897316743356971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_1879
      · exact prime_oneHundredThirteenDG_903757
      · exact prime_oneHundredThirteenDG_1171699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19897316743356971) ^ 9948658371678485 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19897316743356971) ^ 3979463348671394 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19897316743356971) ^ 10589311731430 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19897316743356971) ^ 22016224210 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19897316743356971) ^ 16981594030 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_24539646912758539 : Nat.Prime 24539646912758539 := by
  apply lucas_primality 24539646912758539 (2 : ZMod 24539646912758539)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (371812832011493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (371812832011493, 1)] : List FactorBlock).map factorBlockValue).prod) = 24539646912758539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_371812832011493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24539646912758539) ^ 12269823456379269 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 24539646912758539) ^ 8179882304252846 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 24539646912758539) ^ 2230876992068958 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 24539646912758539) ^ 66 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_28431639190182229 : Nat.Prime 28431639190182229 := by
  apply lucas_primality 28431639190182229 (23 : ZMod 28431639190182229)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (13, 1), (79, 1), (29961219361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (13, 1), (79, 1), (29961219361, 1)] : List FactorBlock).map factorBlockValue).prod) = 28431639190182229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_79
      · exact prime_oneHundredThirteenDG_29961219361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 28431639190182229) ^ 14215819595091114 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (23 : ZMod 28431639190182229) ^ 9477213063394076 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (23 : ZMod 28431639190182229) ^ 4061662741454604 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (23 : ZMod 28431639190182229) ^ 2584694471834748 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (23 : ZMod 28431639190182229) ^ 2187049168475556 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (23 : ZMod 28431639190182229) ^ 359894166964332 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (23 : ZMod 28431639190182229) ^ 948948 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_61245592286912989 : Nat.Prime 61245592286912989 := by
  apply lucas_primality 61245592286912989 (2 : ZMod 61245592286912989)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5309, 1), (961348532161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5309, 1), (961348532161, 1)] : List FactorBlock).map factorBlockValue).prod) = 61245592286912989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5309
      · exact prime_oneHundredThirteenDG_961348532161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61245592286912989) ^ 30622796143456494 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 61245592286912989) ^ 20415197428970996 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 61245592286912989) ^ 11536182385932 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 61245592286912989) ^ 63708 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_63214779142715531 : Nat.Prime 63214779142715531 := by
  apply lucas_primality 63214779142715531 (6 : ZMod 63214779142715531)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (574679810388323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (574679810388323, 1)] : List FactorBlock).map factorBlockValue).prod) = 63214779142715531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_574679810388323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 63214779142715531) ^ 31607389571357765 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 63214779142715531) ^ 12642955828543106 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 63214779142715531) ^ 5746798103883230 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 63214779142715531) ^ 110 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_67376750221315273 : Nat.Prime 67376750221315273 := by
  apply lucas_primality 67376750221315273 (5 : ZMod 67376750221315273)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (53, 1), (5483, 1), (235624717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (53, 1), (5483, 1), (235624717, 1)] : List FactorBlock).map factorBlockValue).prod) = 67376750221315273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_41
      · exact prime_oneHundredThirteenDG_53
      · exact prime_oneHundredThirteenDG_5483
      · exact prime_oneHundredThirteenDG_235624717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 67376750221315273) ^ 33688375110657636 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 67376750221315273) ^ 22458916740438424 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 67376750221315273) ^ 1643335371251592 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 67376750221315273) ^ 1271259438138024 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 67376750221315273) ^ 12288300240984 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 67376750221315273) ^ 285949416 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_80297519267649067 : Nat.Prime 80297519267649067 := by
  apply lucas_primality 80297519267649067 (2 : ZMod 80297519267649067)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (491, 1), (187349, 1), (8557937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (491, 1), (187349, 1), (8557937, 1)] : List FactorBlock).map factorBlockValue).prod) = 80297519267649067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_491
      · exact prime_oneHundredThirteenDG_187349
      · exact prime_oneHundredThirteenDG_8557937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 80297519267649067) ^ 40148759633824533 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 80297519267649067) ^ 26765839755883022 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 80297519267649067) ^ 4723383486332298 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 80297519267649067) ^ 163538735779326 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 80297519267649067) ^ 428598600834 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 80297519267649067) ^ 9382812618 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_87393714970879463 : Nat.Prime 87393714970879463 := by
  apply lucas_primality 87393714970879463 (5 : ZMod 87393714970879463)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7559, 1), (33199, 1), (174124891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7559, 1), (33199, 1), (174124891, 1)] : List FactorBlock).map factorBlockValue).prod) = 87393714970879463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_7559
      · exact prime_oneHundredThirteenDG_33199
      · exact prime_oneHundredThirteenDG_174124891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 87393714970879463) ^ 43696857485439731 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 87393714970879463) ^ 11561544512618 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 87393714970879463) ^ 2632420102138 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 87393714970879463) ^ 501902482 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_94307459431144423 : Nat.Prime 94307459431144423 := by
  apply lucas_primality 94307459431144423 (5 : ZMod 94307459431144423)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (15717909905190737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (15717909905190737, 1)] : List FactorBlock).map factorBlockValue).prod) = 94307459431144423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_15717909905190737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 94307459431144423) ^ 47153729715572211 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 94307459431144423) ^ 31435819810381474 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 94307459431144423) ^ 6 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_183232352376823303 : Nat.Prime 183232352376823303 := by
  apply lucas_primality 183232352376823303 (5 : ZMod 183232352376823303)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (18973237, 1), (25548707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (18973237, 1), (25548707, 1)] : List FactorBlock).map factorBlockValue).prod) = 183232352376823303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_18973237
      · exact prime_oneHundredThirteenDG_25548707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 183232352376823303) ^ 91616176188411651 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 183232352376823303) ^ 61077450792274434 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 183232352376823303) ^ 26176050339546186 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 183232352376823303) ^ 9657411246 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 183232352376823303) ^ 7171883586 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_358637429417089237 : Nat.Prime 358637429417089237 := by
  apply lucas_primality 358637429417089237 (2 : ZMod 358637429417089237)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (126641, 1), (235993496983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (126641, 1), (235993496983, 1)] : List FactorBlock).map factorBlockValue).prod) = 358637429417089237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_126641
      · exact prime_oneHundredThirteenDG_235993496983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 358637429417089237) ^ 179318714708544618 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 358637429417089237) ^ 119545809805696412 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 358637429417089237) ^ 2831921963796 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 358637429417089237) ^ 1519692 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_375914502130378891 : Nat.Prime 375914502130378891 := by
  apply lucas_primality 375914502130378891 (15 : ZMod 375914502130378891)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (61, 1), (636553, 1), (46100473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (61, 1), (636553, 1), (46100473, 1)] : List FactorBlock).map factorBlockValue).prod) = 375914502130378891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_61
      · exact prime_oneHundredThirteenDG_636553
      · exact prime_oneHundredThirteenDG_46100473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 375914502130378891) ^ 187957251065189445 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (15 : ZMod 375914502130378891) ^ 125304834043459630 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (15 : ZMod 375914502130378891) ^ 75182900426075778 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (15 : ZMod 375914502130378891) ^ 53702071732911270 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (15 : ZMod 375914502130378891) ^ 6162532821809490 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (15 : ZMod 375914502130378891) ^ 590547059130 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (15 : ZMod 375914502130378891) ^ 8154243930 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_408255498126427937 : Nat.Prime 408255498126427937 := by
  apply lucas_primality 408255498126427937 (3 : ZMod 408255498126427937)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (12757984316450873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (12757984316450873, 1)] : List FactorBlock).map factorBlockValue).prod) = 408255498126427937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_12757984316450873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 408255498126427937) ^ 204127749063213968 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 408255498126427937) ^ 32 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_429170042096595463 : Nat.Prime 429170042096595463 := by
  apply lucas_primality 429170042096595463 (3 : ZMod 429170042096595463)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (7639, 1), (190577, 1), (3779443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (7639, 1), (190577, 1), (3779443, 1)] : List FactorBlock).map factorBlockValue).prod) = 429170042096595463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_7639
      · exact prime_oneHundredThirteenDG_190577
      · exact prime_oneHundredThirteenDG_3779443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 429170042096595463) ^ 214585021048297731 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 429170042096595463) ^ 143056680698865154 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 429170042096595463) ^ 33013080161276574 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 429170042096595463) ^ 56181442871658 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 429170042096595463) ^ 2251950876006 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 429170042096595463) ^ 113553780834 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_717640790372214061 : Nat.Prime 717640790372214061 := by
  apply lucas_primality 717640790372214061 (2 : ZMod 717640790372214061)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 2), (761, 1), (2029, 1), (64018249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 2), (761, 1), (2029, 1), (64018249, 1)] : List FactorBlock).map factorBlockValue).prod) = 717640790372214061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_761
      · exact prime_oneHundredThirteenDG_2029
      · exact prime_oneHundredThirteenDG_64018249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 717640790372214061) ^ 358820395186107030 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 717640790372214061) ^ 239213596790738020 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 717640790372214061) ^ 143528158074442812 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 717640790372214061) ^ 65240071852019460 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 717640790372214061) ^ 943023377624460 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 717640790372214061) ^ 353691863170140 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 717640790372214061) ^ 11209940940 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1056557421397112711 : Nat.Prime 1056557421397112711 := by
  apply lucas_primality 1056557421397112711 (13 : ZMod 1056557421397112711)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4093, 1), (2575351, 1), (10023397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4093, 1), (2575351, 1), (10023397, 1)] : List FactorBlock).map factorBlockValue).prod) = 1056557421397112711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_4093
      · exact prime_oneHundredThirteenDG_2575351
      · exact prime_oneHundredThirteenDG_10023397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1056557421397112711) ^ 528278710698556355 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 1056557421397112711) ^ 211311484279422542 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 1056557421397112711) ^ 258137654873470 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 1056557421397112711) ^ 410257639210 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 1056557421397112711) ^ 105409116430 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1103175866833115057 : Nat.Prime 1103175866833115057 := by
  apply lucas_primality 1103175866833115057 (3 : ZMod 1103175866833115057)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (401, 1), (769, 1), (13152403867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (401, 1), (769, 1), (13152403867, 1)] : List FactorBlock).map factorBlockValue).prod) = 1103175866833115057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_401
      · exact prime_oneHundredThirteenDG_769
      · exact prime_oneHundredThirteenDG_13152403867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1103175866833115057) ^ 551587933416557528 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1103175866833115057) ^ 64892698049006768 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1103175866833115057) ^ 2751062012052656 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1103175866833115057) ^ 1434558994581424 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1103175866833115057) ^ 83876368 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2408925578029472011 : Nat.Prime 2408925578029472011 := by
  apply lucas_primality 2408925578029472011 (3 : ZMod 2408925578029472011)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (80297519267649067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (80297519267649067, 1)] : List FactorBlock).map factorBlockValue).prod) = 2408925578029472011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_80297519267649067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2408925578029472011) ^ 1204462789014736005 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2408925578029472011) ^ 802975192676490670 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2408925578029472011) ^ 481785115605894402 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2408925578029472011) ^ 30 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_2936093057337518867 : Nat.Prime 2936093057337518867 := by
  apply lucas_primality 2936093057337518867 (2 : ZMod 2936093057337518867)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (59, 1), (14887, 1), (231109, 1), (425417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (59, 1), (14887, 1), (231109, 1), (425417, 1)] : List FactorBlock).map factorBlockValue).prod) = 2936093057337518867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_59
      · exact prime_oneHundredThirteenDG_14887
      · exact prime_oneHundredThirteenDG_231109
      · exact prime_oneHundredThirteenDG_425417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2936093057337518867) ^ 1468046528668759433 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2936093057337518867) ^ 172711356313971698 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2936093057337518867) ^ 49764289107415574 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2936093057337518867) ^ 197225301090718 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2936093057337518867) ^ 12704364855274 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2936093057337518867) ^ 6901682484098 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_3204917065820290589 : Nat.Prime 3204917065820290589 := by
  apply lucas_primality 3204917065820290589 (2 : ZMod 3204917065820290589)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6466367, 1), (123907174841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6466367, 1), (123907174841, 1)] : List FactorBlock).map factorBlockValue).prod) = 3204917065820290589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_6466367
      · exact prime_oneHundredThirteenDG_123907174841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3204917065820290589) ^ 1602458532910145294 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3204917065820290589) ^ 495628699364 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3204917065820290589) ^ 25865468 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_3494271744476513269 : Nat.Prime 3494271744476513269 := by
  apply lucas_primality 3494271744476513269 (2 : ZMod 3494271744476513269)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (61, 1), (521, 1), (38449, 1), (238299331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (61, 1), (521, 1), (38449, 1), (238299331, 1)] : List FactorBlock).map factorBlockValue).prod) = 3494271744476513269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_61
      · exact prime_oneHundredThirteenDG_521
      · exact prime_oneHundredThirteenDG_38449
      · exact prime_oneHundredThirteenDG_238299331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3494271744476513269) ^ 1747135872238256634 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3494271744476513269) ^ 1164757248158837756 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3494271744476513269) ^ 57283143352073988 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3494271744476513269) ^ 6706855555617108 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3494271744476513269) ^ 90880692462132 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3494271744476513269) ^ 14663372028 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_4186448439825379873 : Nat.Prime 4186448439825379873 := by
  apply lucas_primality 4186448439825379873 (7 : ZMod 4186448439825379873)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (111509, 1), (391079087023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (111509, 1), (391079087023, 1)] : List FactorBlock).map factorBlockValue).prod) = 4186448439825379873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_111509
      · exact prime_oneHundredThirteenDG_391079087023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4186448439825379873) ^ 2093224219912689936 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4186448439825379873) ^ 1395482813275126624 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4186448439825379873) ^ 37543592354208 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4186448439825379873) ^ 10704864 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_4646110169657696027 : Nat.Prime 4646110169657696027 := by
  apply lucas_primality 4646110169657696027 (2 : ZMod 4646110169657696027)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (11443621107531271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (11443621107531271, 1)] : List FactorBlock).map factorBlockValue).prod) = 4646110169657696027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_29
      · exact prime_oneHundredThirteenDG_11443621107531271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4646110169657696027) ^ 2323055084828848013 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4646110169657696027) ^ 663730024236813718 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4646110169657696027) ^ 160210695505437794 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4646110169657696027) ^ 406 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_20734937216921912177 : Nat.Prime 20734937216921912177 := by
  apply lucas_primality 20734937216921912177 (3 : ZMod 20734937216921912177)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (326113, 1), (3973878919447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (326113, 1), (3973878919447, 1)] : List FactorBlock).map factorBlockValue).prod) = 20734937216921912177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_326113
      · exact prime_oneHundredThirteenDG_3973878919447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20734937216921912177) ^ 10367468608460956088 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 20734937216921912177) ^ 63582062711152 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 20734937216921912177) ^ 5217808 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_27041961359069588747 : Nat.Prime 27041961359069588747 := by
  apply lucas_primality 27041961359069588747 (2 : ZMod 27041961359069588747)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1117, 1), (12104727555536969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1117, 1), (12104727555536969, 1)] : List FactorBlock).map factorBlockValue).prod) = 27041961359069588747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_1117
      · exact prime_oneHundredThirteenDG_12104727555536969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27041961359069588747) ^ 13520980679534794373 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 27041961359069588747) ^ 24209455111073938 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 27041961359069588747) ^ 2234 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_41876227842508470997 : Nat.Prime 41876227842508470997 := by
  apply lucas_primality 41876227842508470997 (5 : ZMod 41876227842508470997)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (367, 1), (1123, 1), (43319, 1), (5011843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (367, 1), (1123, 1), (43319, 1), (5011843, 1)] : List FactorBlock).map factorBlockValue).prod) = 41876227842508470997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_367
      · exact prime_oneHundredThirteenDG_1123
      · exact prime_oneHundredThirteenDG_43319
      · exact prime_oneHundredThirteenDG_5011843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 41876227842508470997) ^ 20938113921254235498 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 41876227842508470997) ^ 13958742614169490332 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 41876227842508470997) ^ 3221248295577574692 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 41876227842508470997) ^ 114104163058606188 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 41876227842508470997) ^ 37289606271156252 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 41876227842508470997) ^ 966694241383884 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 41876227842508470997) ^ 8355454838172 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_58471986408704023231 : Nat.Prime 58471986408704023231 := by
  apply lucas_primality 58471986408704023231 (3 : ZMod 58471986408704023231)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (89, 1), (1327, 1), (5501035010749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (89, 1), (1327, 1), (5501035010749, 1)] : List FactorBlock).map factorBlockValue).prod) = 58471986408704023231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_89
      · exact prime_oneHundredThirteenDG_1327
      · exact prime_oneHundredThirteenDG_5501035010749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 58471986408704023231) ^ 29235993204352011615 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 58471986408704023231) ^ 19490662136234674410 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 58471986408704023231) ^ 11694397281740804646 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 58471986408704023231) ^ 656988611333753070 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 58471986408704023231) ^ 44063290436099490 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 58471986408704023231) ^ 10629270 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_62896891400577238843 : Nat.Prime 62896891400577238843 := by
  apply lucas_primality 62896891400577238843 (2 : ZMod 62896891400577238843)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3494271744476513269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3494271744476513269, 1)] : List FactorBlock).map factorBlockValue).prod) = 62896891400577238843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_3494271744476513269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 62896891400577238843) ^ 31448445700288619421 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 62896891400577238843) ^ 20965630466859079614 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 62896891400577238843) ^ 18 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_64356440457298558579 : Nat.Prime 64356440457298558579 := by
  apply lucas_primality 64356440457298558579 (26 : ZMod 64356440457298558579)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13693283, 1), (783309116561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13693283, 1), (783309116561, 1)] : List FactorBlock).map factorBlockValue).prod) = 64356440457298558579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_13693283
      · exact prime_oneHundredThirteenDG_783309116561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (26 : ZMod 64356440457298558579) ^ 32178220228649279289 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (26 : ZMod 64356440457298558579) ^ 21452146819099519526 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (26 : ZMod 64356440457298558579) ^ 4699854699366 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (26 : ZMod 64356440457298558579) ^ 82159698 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_71423755404771989291 : Nat.Prime 71423755404771989291 := by
  apply lucas_primality 71423755404771989291 (2 : ZMod 71423755404771989291)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (375914502130378891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (375914502130378891, 1)] : List FactorBlock).map factorBlockValue).prod) = 71423755404771989291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_19
      · exact prime_oneHundredThirteenDG_375914502130378891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 71423755404771989291) ^ 35711877702385994645 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 71423755404771989291) ^ 14284751080954397858 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 71423755404771989291) ^ 3759145021303788910 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 71423755404771989291) ^ 190 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_89172217011053899873 : Nat.Prime 89172217011053899873 := by
  apply lucas_primality 89172217011053899873 (5 : ZMod 89172217011053899873)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (9622489, 1), (32177303971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (9622489, 1), (32177303971, 1)] : List FactorBlock).map factorBlockValue).prod) = 89172217011053899873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_9622489
      · exact prime_oneHundredThirteenDG_32177303971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 89172217011053899873) ^ 44586108505526949936 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 89172217011053899873) ^ 29724072337017966624 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 89172217011053899873) ^ 9267063543648 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 89172217011053899873) ^ 2771276832 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_108939368983891542557 : Nat.Prime 108939368983891542557 := by
  apply lucas_primality 108939368983891542557 (2 : ZMod 108939368983891542557)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (389, 1), (521, 1), (5842647745397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (389, 1), (521, 1), (5842647745397, 1)] : List FactorBlock).map factorBlockValue).prod) = 108939368983891542557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_23
      · exact prime_oneHundredThirteenDG_389
      · exact prime_oneHundredThirteenDG_521
      · exact prime_oneHundredThirteenDG_5842647745397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 108939368983891542557) ^ 54469684491945771278 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 108939368983891542557) ^ 4736494303647458372 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 108939368983891542557) ^ 280049791732369004 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 108939368983891542557) ^ 209096677512267836 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 108939368983891542557) ^ 18645548 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_133260735568285607839 : Nat.Prime 133260735568285607839 := by
  apply lucas_primality 133260735568285607839 (3 : ZMod 133260735568285607839)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (127, 1), (197969, 1), (38408045677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (127, 1), (197969, 1), (38408045677, 1)] : List FactorBlock).map factorBlockValue).prod) = 133260735568285607839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_23
      · exact prime_oneHundredThirteenDG_127
      · exact prime_oneHundredThirteenDG_197969
      · exact prime_oneHundredThirteenDG_38408045677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 133260735568285607839) ^ 66630367784142803919 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133260735568285607839) ^ 44420245189428535946 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133260735568285607839) ^ 5793945024708069906 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133260735568285607839) ^ 1049297130458941794 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133260735568285607839) ^ 673139408535102 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133260735568285607839) ^ 3469604694 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_385040824561486799939 : Nat.Prime 385040824561486799939 := by
  apply lucas_primality 385040824561486799939 (2 : ZMod 385040824561486799939)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (17623, 1), (295253610961019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (17623, 1), (295253610961019, 1)] : List FactorBlock).map factorBlockValue).prod) = 385040824561486799939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_37
      · exact prime_oneHundredThirteenDG_17623
      · exact prime_oneHundredThirteenDG_295253610961019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 385040824561486799939) ^ 192520412280743399969 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 385040824561486799939) ^ 10406508771932075674 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 385040824561486799939) ^ 21848767211115406 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 385040824561486799939) ^ 1304102 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_612364375053910857043 : Nat.Prime 612364375053910857043 := by
  apply lucas_primality 612364375053910857043 (3 : ZMod 612364375053910857043)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (71, 1), (7723, 1), (2954430198833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (71, 1), (7723, 1), (2954430198833, 1)] : List FactorBlock).map factorBlockValue).prod) = 612364375053910857043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_71
      · exact prime_oneHundredThirteenDG_7723
      · exact prime_oneHundredThirteenDG_2954430198833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 612364375053910857043) ^ 306182187526955428521 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 612364375053910857043) ^ 204121458351303619014 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 612364375053910857043) ^ 87480625007701551006 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 612364375053910857043) ^ 8624850352871983902 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 612364375053910857043) ^ 79290997676280054 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 612364375053910857043) ^ 207269874 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1908460487269387263551 : Nat.Prime 1908460487269387263551 := by
  apply lucas_primality 1908460487269387263551 (17 : ZMod 1908460487269387263551)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (2936093057337518867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (2936093057337518867, 1)] : List FactorBlock).map factorBlockValue).prod) = 1908460487269387263551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_2936093057337518867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 1908460487269387263551) ^ 954230243634693631775 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (17 : ZMod 1908460487269387263551) ^ 381692097453877452710 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (17 : ZMod 1908460487269387263551) ^ 146804652866875943350 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (17 : ZMod 1908460487269387263551) ^ 650 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_4276566666617121973807 : Nat.Prime 4276566666617121973807 := by
  apply lucas_primality 4276566666617121973807 (5 : ZMod 4276566666617121973807)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (163, 1), (20101, 1), (1995777996703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (163, 1), (20101, 1), (1995777996703, 1)] : List FactorBlock).map factorBlockValue).prod) = 4276566666617121973807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_109
      · exact prime_oneHundredThirteenDG_163
      · exact prime_oneHundredThirteenDG_20101
      · exact prime_oneHundredThirteenDG_1995777996703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4276566666617121973807) ^ 2138283333308560986903 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4276566666617121973807) ^ 1425522222205707324602 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4276566666617121973807) ^ 39234556574469008934 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4276566666617121973807) ^ 26236605316669459962 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4276566666617121973807) ^ 212753926004533206 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4276566666617121973807) ^ 2142806802 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_4666215187011947681449 : Nat.Prime 4666215187011947681449 := by
  apply lucas_primality 4666215187011947681449 (11 : ZMod 4666215187011947681449)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 1), (97, 1), (131, 1), (1747, 1), (139019920801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 1), (97, 1), (131, 1), (1747, 1), (139019920801, 1)] : List FactorBlock).map factorBlockValue).prod) = 4666215187011947681449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_97
      · exact prime_oneHundredThirteenDG_131
      · exact prime_oneHundredThirteenDG_1747
      · exact prime_oneHundredThirteenDG_139019920801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4666215187011947681449) ^ 2333107593505973840724 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 4666215187011947681449) ^ 1555405062337315893816 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 4666215187011947681449) ^ 666602169573135383064 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 4666215187011947681449) ^ 48105311206308738984 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 4666215187011947681449) ^ 35619963259633188408 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 4666215187011947681449) ^ 2670987514030880184 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (11 : ZMod 4666215187011947681449) ^ 33565083048 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_8259745676824257438253 : Nat.Prime 8259745676824257438253 := by
  apply lucas_primality 8259745676824257438253 (5 : ZMod 8259745676824257438253)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (277007, 1), (2484818577636503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (277007, 1), (2484818577636503, 1)] : List FactorBlock).map factorBlockValue).prod) = 8259745676824257438253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_277007
      · exact prime_oneHundredThirteenDG_2484818577636503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 8259745676824257438253) ^ 4129872838412128719126 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8259745676824257438253) ^ 2753248558941419146084 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8259745676824257438253) ^ 29817822931638036 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8259745676824257438253) ^ 3324084 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_25879508806670235076147 : Nat.Prime 25879508806670235076147 := by
  apply lucas_primality 25879508806670235076147 (5 : ZMod 25879508806670235076147)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (41876227842508470997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (41876227842508470997, 1)] : List FactorBlock).map factorBlockValue).prod) = 25879508806670235076147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_103
      · exact prime_oneHundredThirteenDG_41876227842508470997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 25879508806670235076147) ^ 12939754403335117538073 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 25879508806670235076147) ^ 8626502935556745025382 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 25879508806670235076147) ^ 251257367055050825982 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 25879508806670235076147) ^ 618 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_27813115865073973213447 : Nat.Prime 27813115865073973213447 := by
  apply lucas_primality 27813115865073973213447 (3 : ZMod 27813115865073973213447)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1027489, 1), (4511502615449569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1027489, 1), (4511502615449569, 1)] : List FactorBlock).map factorBlockValue).prod) = 27813115865073973213447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_1027489
      · exact prime_oneHundredThirteenDG_4511502615449569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 27813115865073973213447) ^ 13906557932536986606723 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 27813115865073973213447) ^ 9271038621691324404482 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 27813115865073973213447) ^ 27069015692697414 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 27813115865073973213447) ^ 6164934 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_34920125209923804580937 : Nat.Prime 34920125209923804580937 := by
  apply lucas_primality 34920125209923804580937 (3 : ZMod 34920125209923804580937)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (457, 1), (52361, 1), (9600814353859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (457, 1), (52361, 1), (9600814353859, 1)] : List FactorBlock).map factorBlockValue).prod) = 34920125209923804580937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_19
      · exact prime_oneHundredThirteenDG_457
      · exact prime_oneHundredThirteenDG_52361
      · exact prime_oneHundredThirteenDG_9600814353859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34920125209923804580937) ^ 17460062604961902290468 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 34920125209923804580937) ^ 1837901326838094977944 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 34920125209923804580937) ^ 76411652538126487048 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 34920125209923804580937) ^ 666910968276461576 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 34920125209923804580937) ^ 3637204504 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_45618534053923933109827 : Nat.Prime 45618534053923933109827 := by
  apply lucas_primality 45618534053923933109827 (3 : ZMod 45618534053923933109827)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 1), (17, 1), (859, 1), (3528659, 1), (540475051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 1), (17, 1), (859, 1), (3528659, 1), (540475051, 1)] : List FactorBlock).map factorBlockValue).prod) = 45618534053923933109827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_859
      · exact prime_oneHundredThirteenDG_3528659
      · exact prime_oneHundredThirteenDG_540475051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 45618534053923933109827) ^ 22809267026961966554913 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 45618534053923933109827) ^ 15206178017974644369942 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 45618534053923933109827) ^ 6516933436274847587118 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 45618534053923933109827) ^ 3509118004147994854602 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 45618534053923933109827) ^ 2683443179642584300578 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 45618534053923933109827) ^ 53106558852065114214 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 45618534053923933109827) ^ 12928008644055414 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 45618534053923933109827) ^ 84404514083526 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_98725297018439056665061 : Nat.Prime 98725297018439056665061 := by
  apply lucas_primality 98725297018439056665061 (6 : ZMod 98725297018439056665061)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (916339, 1), (598549087537103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (916339, 1), (598549087537103, 1)] : List FactorBlock).map factorBlockValue).prod) = 98725297018439056665061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_916339
      · exact prime_oneHundredThirteenDG_598549087537103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 98725297018439056665061) ^ 49362648509219528332530 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 98725297018439056665061) ^ 32908432339479685555020 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 98725297018439056665061) ^ 19745059403687811333012 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 98725297018439056665061) ^ 107738835756678540 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (6 : ZMod 98725297018439056665061) ^ 164941020 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_132969737470395899227523 : Nat.Prime 132969737470395899227523 := by
  apply lucas_primality 132969737470395899227523 (2 : ZMod 132969737470395899227523)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (62775767, 1), (1059084928985383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (62775767, 1), (1059084928985383, 1)] : List FactorBlock).map factorBlockValue).prod) = 132969737470395899227523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_62775767
      · exact prime_oneHundredThirteenDG_1059084928985383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 132969737470395899227523) ^ 66484868735197949613761 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 132969737470395899227523) ^ 2118169857970766 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 132969737470395899227523) ^ 125551534 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_149603425192349999561909 : Nat.Prime 149603425192349999561909 := by
  apply lucas_primality 149603425192349999561909 (2 : ZMod 149603425192349999561909)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (41, 1), (43, 1), (305529307, 1), (9919238171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (41, 1), (43, 1), (305529307, 1), (9919238171, 1)] : List FactorBlock).map factorBlockValue).prod) = 149603425192349999561909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_41
      · exact prime_oneHundredThirteenDG_43
      · exact prime_oneHundredThirteenDG_305529307
      · exact prime_oneHundredThirteenDG_9919238171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 149603425192349999561909) ^ 74801712596174999780954 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 149603425192349999561909) ^ 21371917884621428508844 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 149603425192349999561909) ^ 3648864029081707306388 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 149603425192349999561909) ^ 3479149423077906966556 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 149603425192349999561909) ^ 489653273073244 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 149603425192349999561909) ^ 15082148710748 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_395019996699060423561089 : Nat.Prime 395019996699060423561089 := by
  apply lucas_primality 395019996699060423561089 (3 : ZMod 395019996699060423561089)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (43, 1), (3607, 1), (19897316743356971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (43, 1), (3607, 1), (19897316743356971, 1)] : List FactorBlock).map factorBlockValue).prod) = 395019996699060423561089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_43
      · exact prime_oneHundredThirteenDG_3607
      · exact prime_oneHundredThirteenDG_19897316743356971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 395019996699060423561089) ^ 197509998349530211780544 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 395019996699060423561089) ^ 9186511551140940082816 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 395019996699060423561089) ^ 109514831355436768384 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 395019996699060423561089) ^ 19852928 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_3366075182131546128871573 : Nat.Prime 3366075182131546128871573 := by
  apply lucas_primality 3366075182131546128871573 (2 : ZMod 3366075182131546128871573)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (23, 1), (41, 1), (27041961359069588747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (23, 1), (41, 1), (27041961359069588747, 1)] : List FactorBlock).map factorBlockValue).prod) = 3366075182131546128871573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_23
      · exact prime_oneHundredThirteenDG_41
      · exact prime_oneHundredThirteenDG_27041961359069588747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3366075182131546128871573) ^ 1683037591065773064435786 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3366075182131546128871573) ^ 1122025060710515376290524 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3366075182131546128871573) ^ 306006834739231466261052 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3366075182131546128871573) ^ 146351094875284614298764 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3366075182131546128871573) ^ 82099394686135271435892 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3366075182131546128871573) ^ 124476 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_3994622590109404805309887 : Nat.Prime 3994622590109404805309887 := by
  apply lucas_primality 3994622590109404805309887 (3 : ZMod 3994622590109404805309887)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (9007, 1), (717640790372214061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (9007, 1), (717640790372214061, 1)] : List FactorBlock).map factorBlockValue).prod) = 3994622590109404805309887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_103
      · exact prime_oneHundredThirteenDG_9007
      · exact prime_oneHundredThirteenDG_717640790372214061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3994622590109404805309887) ^ 1997311295054702402654943 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3994622590109404805309887) ^ 1331540863369801601769962 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3994622590109404805309887) ^ 38782743593295192284562 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3994622590109404805309887) ^ 443502008450028289698 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3994622590109404805309887) ^ 5566326 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_5804742902612163124431191 : Nat.Prime 5804742902612163124431191 := by
  apply lucas_primality 5804742902612163124431191 (7 : ZMod 5804742902612163124431191)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (73, 1), (181, 1), (281, 1), (14212895049641593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (73, 1), (181, 1), (281, 1), (14212895049641593, 1)] : List FactorBlock).map factorBlockValue).prod) = 5804742902612163124431191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_73
      · exact prime_oneHundredThirteenDG_181
      · exact prime_oneHundredThirteenDG_281
      · exact prime_oneHundredThirteenDG_14212895049641593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5804742902612163124431191) ^ 2902371451306081562215595 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 5804742902612163124431191) ^ 1160948580522432624886238 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 5804742902612163124431191) ^ 527703900237469374948290 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 5804742902612163124431191) ^ 79517026063180316773030 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 5804742902612163124431191) ^ 32070402776862779692990 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 5804742902612163124431191) ^ 20657448052000580513990 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 5804742902612163124431191) ^ 408413830 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_6579795011013540893852633 : Nat.Prime 6579795011013540893852633 := by
  apply lucas_primality 6579795011013540893852633 (3 : ZMod 6579795011013540893852633)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (36599, 1), (27750607, 1), (115686486229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (36599, 1), (27750607, 1), (115686486229, 1)] : List FactorBlock).map factorBlockValue).prod) = 6579795011013540893852633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_36599
      · exact prime_oneHundredThirteenDG_27750607
      · exact prime_oneHundredThirteenDG_115686486229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6579795011013540893852633) ^ 3289897505506770446926316 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6579795011013540893852633) ^ 939970715859077270550376 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6579795011013540893852633) ^ 179780732014905896168 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6579795011013540893852633) ^ 237104543731729576 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6579795011013540893852633) ^ 56876090073208 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_6738432255806462943043673 : Nat.Prime 6738432255806462943043673 := by
  apply lucas_primality 6738432255806462943043673 (3 : ZMod 6738432255806462943043673)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (277, 1), (613, 1), (755617, 1), (6564881871827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (277, 1), (613, 1), (755617, 1), (6564881871827, 1)] : List FactorBlock).map factorBlockValue).prod) = 6738432255806462943043673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_277
      · exact prime_oneHundredThirteenDG_613
      · exact prime_oneHundredThirteenDG_755617
      · exact prime_oneHundredThirteenDG_6564881871827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6738432255806462943043673) ^ 3369216127903231471521836 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6738432255806462943043673) ^ 24326470237568458278136 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6738432255806462943043673) ^ 10992548541282973805944 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6738432255806462943043673) ^ 8917788053744771416 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6738432255806462943043673) ^ 1026436177736 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_11879437835996704100016349 : Nat.Prime 11879437835996704100016349 := by
  apply lucas_primality 11879437835996704100016349 (2 : ZMod 11879437835996704100016349)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (9161, 1), (46337, 1), (2332082163085397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (9161, 1), (46337, 1), (2332082163085397, 1)] : List FactorBlock).map factorBlockValue).prod) = 11879437835996704100016349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_9161
      · exact prime_oneHundredThirteenDG_46337
      · exact prime_oneHundredThirteenDG_2332082163085397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11879437835996704100016349) ^ 5939718917998352050008174 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11879437835996704100016349) ^ 3959812611998901366672116 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11879437835996704100016349) ^ 1296740294290656489468 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11879437835996704100016349) ^ 256370456352303863004 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11879437835996704100016349) ^ 5093919084 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_12687194482774827569685077 : Nat.Prime 12687194482774827569685077 := by
  apply lucas_primality 12687194482774827569685077 (2 : ZMod 12687194482774827569685077)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (47, 1), (269, 1), (99761, 1), (228613561254373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (47, 1), (269, 1), (99761, 1), (228613561254373, 1)] : List FactorBlock).map factorBlockValue).prod) = 12687194482774827569685077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_47
      · exact prime_oneHundredThirteenDG_269
      · exact prime_oneHundredThirteenDG_99761
      · exact prime_oneHundredThirteenDG_228613561254373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12687194482774827569685077) ^ 6343597241387413784842538 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12687194482774827569685077) ^ 1153381316615893415425916 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12687194482774827569685077) ^ 269940308144145267440108 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12687194482774827569685077) ^ 47164291757527240036004 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12687194482774827569685077) ^ 127175895217317664916 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12687194482774827569685077) ^ 55496246212 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_15266387601830526146587117 : Nat.Prime 15266387601830526146587117 := by
  apply lucas_primality 15266387601830526146587117 (2 : ZMod 15266387601830526146587117)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (83, 1), (1427, 1), (250841, 1), (14273589247651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (83, 1), (1427, 1), (250841, 1), (14273589247651, 1)] : List FactorBlock).map factorBlockValue).prod) = 15266387601830526146587117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_83
      · exact prime_oneHundredThirteenDG_1427
      · exact prime_oneHundredThirteenDG_250841
      · exact prime_oneHundredThirteenDG_14273589247651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15266387601830526146587117) ^ 7633193800915263073293558 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15266387601830526146587117) ^ 5088795867276842048862372 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15266387601830526146587117) ^ 183932380744946098151652 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15266387601830526146587117) ^ 10698239384604433179108 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15266387601830526146587117) ^ 60860814626917155276 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15266387601830526146587117) ^ 1069554919716 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_22651094931098496830923001 : Nat.Prime 22651094931098496830923001 := by
  apply lucas_primality 22651094931098496830923001 (3 : ZMod 22651094931098496830923001)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (513269, 1), (3767831, 1), (11712584857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (513269, 1), (3767831, 1), (11712584857, 1)] : List FactorBlock).map factorBlockValue).prod) = 22651094931098496830923001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_513269
      · exact prime_oneHundredThirteenDG_3767831
      · exact prime_oneHundredThirteenDG_11712584857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 22651094931098496830923001) ^ 11325547465549248415461500 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 22651094931098496830923001) ^ 4530218986219699366184600 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 22651094931098496830923001) ^ 44131040314335167000 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 22651094931098496830923001) ^ 6011706716967533000 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 22651094931098496830923001) ^ 1933910849539000 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_135906569586590980985538007 : Nat.Prime 135906569586590980985538007 := by
  apply lucas_primality 135906569586590980985538007 (5 : ZMod 135906569586590980985538007)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (22651094931098496830923001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (22651094931098496830923001, 1)] : List FactorBlock).map factorBlockValue).prod) = 135906569586590980985538007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_22651094931098496830923001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 135906569586590980985538007) ^ 67953284793295490492769003 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 135906569586590980985538007) ^ 45302189862196993661846002 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 135906569586590980985538007) ^ 6 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_355308930594731208268042183 : Nat.Prime 355308930594731208268042183 := by
  apply lucas_primality 355308930594731208268042183 (3 : ZMod 355308930594731208268042183)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (6579795011013540893852633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (6579795011013540893852633, 1)] : List FactorBlock).map factorBlockValue).prod) = 355308930594731208268042183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_6579795011013540893852633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 355308930594731208268042183) ^ 177654465297365604134021091 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 355308930594731208268042183) ^ 118436310198243736089347394 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 355308930594731208268042183) ^ 54 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_366016870968818998106257153 : Nat.Prime 366016870968818998106257153 := by
  apply lucas_primality 366016870968818998106257153 (10 : ZMod 366016870968818998106257153)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (37, 1), (5294539, 1), (2432820172120523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (37, 1), (5294539, 1), (2432820172120523, 1)] : List FactorBlock).map factorBlockValue).prod) = 366016870968818998106257153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_37
      · exact prime_oneHundredThirteenDG_5294539
      · exact prime_oneHundredThirteenDG_2432820172120523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 366016870968818998106257153) ^ 183008435484409499053128576 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 366016870968818998106257153) ^ 122005623656272999368752384 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 366016870968818998106257153) ^ 9892347864022135083952896 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 366016870968818998106257153) ^ 69131018010976781568 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 366016870968818998106257153) ^ 150449620224 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_536530754633007768308368919 : Nat.Prime 536530754633007768308368919 := by
  apply lucas_primality 536530754633007768308368919 (7 : ZMod 536530754633007768308368919)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (43, 1), (191, 1), (4666215187011947681449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (43, 1), (191, 1), (4666215187011947681449, 1)] : List FactorBlock).map factorBlockValue).prod) = 536530754633007768308368919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_43
      · exact prime_oneHundredThirteenDG_191
      · exact prime_oneHundredThirteenDG_4666215187011947681449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 536530754633007768308368919) ^ 268265377316503884154184459 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 536530754633007768308368919) ^ 76647250661858252615481274 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 536530754633007768308368919) ^ 12477459410069948100194626 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 536530754633007768308368919) ^ 2809061542581192504232298 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 536530754633007768308368919) ^ 114982 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_549778427586909194686353337 : Nat.Prime 549778427586909194686353337 := by
  apply lucas_primality 549778427586909194686353337 (5 : ZMod 549778427586909194686353337)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (9509399, 1), (2408925578029472011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (9509399, 1), (2408925578029472011, 1)] : List FactorBlock).map factorBlockValue).prod) = 549778427586909194686353337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_9509399
      · exact prime_oneHundredThirteenDG_2408925578029472011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 549778427586909194686353337) ^ 274889213793454597343176668 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 549778427586909194686353337) ^ 183259475862303064895451112 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 549778427586909194686353337) ^ 57814213872707328264 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (5 : ZMod 549778427586909194686353337) ^ 228225576 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1192822838425169056328427329 : Nat.Prime 1192822838425169056328427329 := by
  apply lucas_primality 1192822838425169056328427329 (3 : ZMod 1192822838425169056328427329)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (16109939, 1), (279067751, 1), (4145647993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (16109939, 1), (279067751, 1), (4145647993, 1)] : List FactorBlock).map factorBlockValue).prod) = 1192822838425169056328427329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_16109939
      · exact prime_oneHundredThirteenDG_279067751
      · exact prime_oneHundredThirteenDG_4145647993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1192822838425169056328427329) ^ 596411419212584528164213664 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1192822838425169056328427329) ^ 74042666358027119552 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1192822838425169056328427329) ^ 4274312722092955328 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1192822838425169056328427329) ^ 287728924510540096 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1322734236669494399096869909 : Nat.Prime 1322734236669494399096869909 := by
  apply lucas_primality 1322734236669494399096869909 (2 : ZMod 1322734236669494399096869909)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (197, 1), (239870509, 1), (30294064138579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (197, 1), (239870509, 1), (30294064138579, 1)] : List FactorBlock).map factorBlockValue).prod) = 1322734236669494399096869909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_197
      · exact prime_oneHundredThirteenDG_239870509
      · exact prime_oneHundredThirteenDG_30294064138579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1322734236669494399096869909) ^ 661367118334747199548434954 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1322734236669494399096869909) ^ 440911412223164799698956636 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1322734236669494399096869909) ^ 188962033809927771299552844 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1322734236669494399096869909) ^ 120248566969954036281533628 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1322734236669494399096869909) ^ 6714386988170022330440964 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1322734236669494399096869909) ^ 5514367907017258212 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1322734236669494399096869909) ^ 43663149012252 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1436517826920633702244987751 : Nat.Prime 1436517826920633702244987751 := by
  apply lucas_primality 1436517826920633702244987751 (7 : ZMod 1436517826920633702244987751)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (7, 1), (31, 1), (421, 1), (62896891400577238843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (7, 1), (31, 1), (421, 1), (62896891400577238843, 1)] : List FactorBlock).map factorBlockValue).prod) = 1436517826920633702244987751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_31
      · exact prime_oneHundredThirteenDG_421
      · exact prime_oneHundredThirteenDG_62896891400577238843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1436517826920633702244987751) ^ 718258913460316851122493875 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1436517826920633702244987751) ^ 287303565384126740448997550 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1436517826920633702244987751) ^ 205216832417233386034998250 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1436517826920633702244987751) ^ 46339284739375280717580250 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1436517826920633702244987751) ^ 3412156358481315207232750 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1436517826920633702244987751) ^ 22839250 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_1781282105381585790783784811 : Nat.Prime 1781282105381585790783784811 := by
  apply lucas_primality 1781282105381585790783784811 (7 : ZMod 1781282105381585790783784811)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 2), (421, 1), (62896891400577238843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 2), (421, 1), (62896891400577238843, 1)] : List FactorBlock).map factorBlockValue).prod) = 1781282105381585790783784811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_31
      · exact prime_oneHundredThirteenDG_421
      · exact prime_oneHundredThirteenDG_62896891400577238843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1781282105381585790783784811) ^ 890641052690792895391892405 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1781282105381585790783784811) ^ 356256421076317158156756962 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1781282105381585790783784811) ^ 254468872197369398683397830 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1781282105381585790783784811) ^ 57460713076825348089799510 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1781282105381585790783784811) ^ 4231073884516830856968610 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1781282105381585790783784811) ^ 28320670 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_7031376731769417595199150569 : Nat.Prime 7031376731769417595199150569 := by
  apply lucas_primality 7031376731769417595199150569 (13 : ZMod 7031376731769417595199150569)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (2045909, 1), (4188739, 1), (1627946835517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (2045909, 1), (4188739, 1), (1627946835517, 1)] : List FactorBlock).map factorBlockValue).prod) = 7031376731769417595199150569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_2045909
      · exact prime_oneHundredThirteenDG_4188739
      · exact prime_oneHundredThirteenDG_1627946835517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 7031376731769417595199150569) ^ 3515688365884708797599575284 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 7031376731769417595199150569) ^ 2343792243923139198399716856 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 7031376731769417595199150569) ^ 1004482390252773942171307224 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 7031376731769417595199150569) ^ 3436798377527748103752 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 7031376731769417595199150569) ^ 1678638065482097976312 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (13 : ZMod 7031376731769417595199150569) ^ 4319168524650504 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_14844017544846548256531540089 : Nat.Prime 14844017544846548256531540089 := by
  apply lucas_primality 14844017544846548256531540089 (3 : ZMod 14844017544846548256531540089)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (19, 1), (2045909, 1), (4188739, 1), (1627946835517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (19, 1), (2045909, 1), (4188739, 1), (1627946835517, 1)] : List FactorBlock).map factorBlockValue).prod) = 14844017544846548256531540089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_19
      · exact prime_oneHundredThirteenDG_2045909
      · exact prime_oneHundredThirteenDG_4188739
      · exact prime_oneHundredThirteenDG_1627946835517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14844017544846548256531540089) ^ 7422008772423274128265770044 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14844017544846548256531540089) ^ 2120573934978078322361648584 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14844017544846548256531540089) ^ 781264081307713066133238952 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14844017544846548256531540089) ^ 7255463241447468219032 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14844017544846548256531540089) ^ 3543791471573317949992 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14844017544846548256531540089) ^ 9118244663151064 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_19085165414802704901254837257 : Nat.Prime 19085165414802704901254837257 := by
  apply lucas_primality 19085165414802704901254837257 (7 : ZMod 19085165414802704901254837257)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (19, 1), (2045909, 1), (4188739, 1), (1627946835517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (19, 1), (2045909, 1), (4188739, 1), (1627946835517, 1)] : List FactorBlock).map factorBlockValue).prod) = 19085165414802704901254837257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_19
      · exact prime_oneHundredThirteenDG_2045909
      · exact prime_oneHundredThirteenDG_4188739
      · exact prime_oneHundredThirteenDG_1627946835517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 19085165414802704901254837257) ^ 9542582707401352450627418628 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 19085165414802704901254837257) ^ 6361721804934234967084945752 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 19085165414802704901254837257) ^ 1004482390252773942171307224 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 19085165414802704901254837257) ^ 9328452739003887710184 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 19085165414802704901254837257) ^ 4556303320594265935704 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 19085165414802704901254837257) ^ 11723457424051368 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_44532052634539644769594620293 : Nat.Prime 44532052634539644769594620293 := by
  apply lucas_primality 44532052634539644769594620293 (2 : ZMod 44532052634539644769594620293)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (149, 1), (7369, 1), (29927, 1), (14989493, 1), (3229012529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (149, 1), (7369, 1), (29927, 1), (14989493, 1), (3229012529, 1)] : List FactorBlock).map factorBlockValue).prod) = 44532052634539644769594620293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_149
      · exact prime_oneHundredThirteenDG_7369
      · exact prime_oneHundredThirteenDG_29927
      · exact prime_oneHundredThirteenDG_14989493
      · exact prime_oneHundredThirteenDG_3229012529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44532052634539644769594620293) ^ 22266026317269822384797310146 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44532052634539644769594620293) ^ 6361721804934234967084945756 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44532052634539644769594620293) ^ 298872836473420434695265908 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44532052634539644769594620293) ^ 6043160894902923703296868 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44532052634539644769594620293) ^ 1488022609501107520619996 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44532052634539644769594620293) ^ 2970884514542262688244 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44532052634539644769594620293) ^ 13791229434569854148 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_133596157903618934308783860817 : Nat.Prime 133596157903618934308783860817 := by
  apply lucas_primality 133596157903618934308783860817 (10 : ZMod 133596157903618934308783860817)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (53, 1), (911, 1), (17483, 1), (327825787, 1), (10057717069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (53, 1), (911, 1), (17483, 1), (327825787, 1), (10057717069, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_3
      · exact prime_oneHundredThirteenDG_53
      · exact prime_oneHundredThirteenDG_911
      · exact prime_oneHundredThirteenDG_17483
      · exact prime_oneHundredThirteenDG_327825787
      · exact prime_oneHundredThirteenDG_10057717069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 133596157903618934308783860817) ^ 66798078951809467154391930408 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 133596157903618934308783860817) ^ 44532052634539644769594620272 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 133596157903618934308783860817) ^ 2520682224596583666203469072 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 133596157903618934308783860817) ^ 146647813286080059614471856 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 133596157903618934308783860817) ^ 7641489326981578350899952 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 133596157903618934308783860817) ^ 407521809453076777968 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (10 : ZMod 133596157903618934308783860817) ^ 13282950493347083664 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_133596157903618934308783860821 : Nat.Prime 133596157903618934308783860821 := by
  apply lucas_primality 133596157903618934308783860821 (3 : ZMod 133596157903618934308783860821)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (619, 1), (967, 1), (155461, 1), (4334593, 1), (2365805447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (619, 1), (967, 1), (155461, 1), (4334593, 1), (2365805447, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_5
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_619
      · exact prime_oneHundredThirteenDG_967
      · exact prime_oneHundredThirteenDG_155461
      · exact prime_oneHundredThirteenDG_4334593
      · exact prime_oneHundredThirteenDG_2365805447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 133596157903618934308783860821) ^ 66798078951809467154391930410 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133596157903618934308783860821) ^ 26719231580723786861756772164 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133596157903618934308783860821) ^ 19085165414802704901254837260 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133596157903618934308783860821) ^ 215825780135087131355062780 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133596157903618934308783860821) ^ 138155282216772424311048460 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133596157903618934308783860821) ^ 859354808624792933975620 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133596157903618934308783860821) ^ 30820923187856145734740 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133596157903618934308783860821) ^ 56469629856093122060 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_133596157903618934308783860857 : Nat.Prime 133596157903618934308783860857 := by
  apply lucas_primality 133596157903618934308783860857 (3 : ZMod 133596157903618934308783860857)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (29, 1), (17749, 1), (1908460487269387263551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (29, 1), (17749, 1), (1908460487269387263551, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_17
      · exact prime_oneHundredThirteenDG_29
      · exact prime_oneHundredThirteenDG_17749
      · exact prime_oneHundredThirteenDG_1908460487269387263551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 133596157903618934308783860857) ^ 66798078951809467154391930428 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133596157903618934308783860857) ^ 7858597523742290253457874168 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133596157903618934308783860857) ^ 4606764065642032217544271064 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133596157903618934308783860857) ^ 7526968161790463367445144 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133596157903618934308783860857) ^ 70002056 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_133596157903618934308783860863 : Nat.Prime 133596157903618934308783860863 := by
  apply lucas_primality 133596157903618934308783860863 (7 : ZMod 133596157903618934308783860863)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (11, 2), (13, 1), (29573, 1), (4186448439825379873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (11, 2), (13, 1), (29573, 1), (4186448439825379873, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_7
      · exact prime_oneHundredThirteenDG_11
      · exact prime_oneHundredThirteenDG_13
      · exact prime_oneHundredThirteenDG_29573
      · exact prime_oneHundredThirteenDG_4186448439825379873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 133596157903618934308783860863) ^ 66798078951809467154391930431 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 133596157903618934308783860863) ^ 19085165414802704901254837266 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 133596157903618934308783860863) ^ 12145105263965357664434896442 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 133596157903618934308783860863) ^ 10276627531047610331444912374 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 133596157903618934308783860863) ^ 4517504409549891262597094 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (7 : ZMod 133596157903618934308783860863) ^ 31911573694 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirteenDG_133596157903618934308783860893 : Nat.Prime 133596157903618934308783860893 := by
  apply lucas_primality 133596157903618934308783860893 (2 : ZMod 133596157903618934308783860893)
  · rw [← oneHundredThirteenDGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (89, 1), (281, 1), (6299, 1), (7457, 1), (28431639190182229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (89, 1), (281, 1), (6299, 1), (7457, 1), (28431639190182229, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirteenDG_2
      · exact prime_oneHundredThirteenDG_89
      · exact prime_oneHundredThirteenDG_281
      · exact prime_oneHundredThirteenDG_6299
      · exact prime_oneHundredThirteenDG_7457
      · exact prime_oneHundredThirteenDG_28431639190182229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 133596157903618934308783860893) ^ 66798078951809467154391930446 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 133596157903618934308783860893) ^ 1501080425883358812458245628 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 133596157903618934308783860893) ^ 475431166916793360529479932 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 133596157903618934308783860893) ^ 21209105874522770965039508 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 133596157903618934308783860893) ^ 17915536798125108530076956 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide
    · change (2 : ZMod 133596157903618934308783860893) ^ 4698855279148 ≠ 1
      rw [← oneHundredThirteenDGFastPow_eq_pow]
      decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860797 : Nat.totient 133596157903618934308783860797 = 118755132425600947426589060160 := by
  rw [← show ((([(13, 1), (43, 1), (71, 1), (3366075182131546128871573, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860797 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_13, prime_oneHundredThirteenDG_43, prime_oneHundredThirteenDG_71, prime_oneHundredThirteenDG_3366075182131546128871573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860798 : Nat.totient 133596157903618934308783860798 = 42996463451502483214045824000 := by
  rw [← show ((([(2, 1), (3, 1), (29, 1), (37029001, 1), (20734937216921912177, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860798 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_29, prime_oneHundredThirteenDG_37029001, prime_oneHundredThirteenDG_20734937216921912177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860799 : Nat.totient 133596157903618934308783860799 = 114510992488816229407529023536 := by
  rw [← show ((([(7, 1), (19085165414802704901254837257, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860799 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_7, prime_oneHundredThirteenDG_19085165414802704901254837257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860800 : Nat.totient 133596157903618934308783860800 = 52965247309410099091857408000 := by
  rw [← show ((([(2, 6), (5, 2), (113, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_113, prime_oneHundredThirteenDG_171401, prime_oneHundredThirteenDG_714027719, prime_oneHundredThirteenDG_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860801 : Nat.totient 133596157903618934308783860801 = 89064105269079289539189240528 := by
  rw [← show ((([(3, 2), (14844017544846548256531540089, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_14844017544846548256531540089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860802 : Nat.totient 133596157903618934308783860802 = 66790884497117431378740566400 := by
  rw [← show ((([(2, 1), (10243, 1), (99719, 1), (20132201, 1), (3248385981653, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_10243, prime_oneHundredThirteenDG_99719, prime_oneHundredThirteenDG_20132201, prime_oneHundredThirteenDG_3248385981653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860803 : Nat.totient 133596157903618934308783860803 = 129056196042037007940317552640 := by
  rw [← show ((([(61, 1), (89, 1), (163, 1), (1693, 1), (89172217011053899873, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_61, prime_oneHundredThirteenDG_89, prime_oneHundredThirteenDG_163, prime_oneHundredThirteenDG_1693, prime_oneHundredThirteenDG_89172217011053899873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860804 : Nat.totient 133596157903618934308783860804 = 44527297947395882955472765440 := by
  rw [← show ((([(2, 2), (3, 1), (10853, 1), (74891, 1), (1834069, 1), (2585899, 1), (2888059, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_10853, prime_oneHundredThirteenDG_74891, prime_oneHundredThirteenDG_1834069, prime_oneHundredThirteenDG_2585899, prime_oneHundredThirteenDG_2888059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860805 : Nat.totient 133596157903618934308783860805 = 100589774603634651748430944512 := by
  rw [← show ((([(5, 1), (17, 1), (367519, 1), (4276566666617121973807, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_17, prime_oneHundredThirteenDG_367519, prime_oneHundredThirteenDG_4276566666617121973807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860806 : Nat.totient 133596157903618934308783860806 = 54538881497398479704335971840 := by
  rw [← show ((([(2, 1), (7, 1), (23, 1), (241, 1), (9946559327, 1), (173080514215789, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_7, prime_oneHundredThirteenDG_23, prime_oneHundredThirteenDG_241, prime_oneHundredThirteenDG_9946559327, prime_oneHundredThirteenDG_173080514215789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860807 : Nat.totient 133596157903618934308783860807 = 80967368426427108078089071680 := by
  rw [← show ((([(3, 1), (11, 1), (9619159692313, 1), (420865080819583, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_11, prime_oneHundredThirteenDG_9619159692313, prime_oneHundredThirteenDG_420865080819583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860808 : Nat.totient 133596157903618934308783860808 = 65376843229430542321319761488 := by
  rw [← show ((([(2, 3), (47, 1), (355308930594731208268042183, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_47, prime_oneHundredThirteenDG_355308930594731208268042183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860809 : Nat.totient 133596157903618934308783860809 = 132273423666949439909686990800 := by
  rw [← show ((([(101, 1), (1322734236669494399096869909, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_101, prime_oneHundredThirteenDG_1322734236669494399096869909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860810 : Nat.totient 133596157903618934308783860810 = 32885208099352353060623716992 := by
  rw [← show ((([(2, 1), (3, 4), (5, 1), (13, 1), (12687194482774827569685077, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_13, prime_oneHundredThirteenDG_12687194482774827569685077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860811 : Nat.totient 133596157903618934308783860811 = 126564781171849516713584710224 := by
  rw [← show ((([(19, 1), (7031376731769417595199150569, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_19, prime_oneHundredThirteenDG_7031376731769417595199150569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860812 : Nat.totient 133596157903618934308783860812 = 64275626393358647444133727680 := by
  rw [← show ((([(2, 2), (31, 1), (179, 1), (9829, 1), (612364375053910857043, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_31, prime_oneHundredThirteenDG_179, prime_oneHundredThirteenDG_9829, prime_oneHundredThirteenDG_612364375053910857043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860813 : Nat.totient 133596157903618934308783860813 = 74184945960526826799156854400 := by
  rw [← show ((([(3, 1), (7, 2), (37, 1), (827, 1), (28111, 1), (1056557421397112711, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_7, prime_oneHundredThirteenDG_37, prime_oneHundredThirteenDG_827, prime_oneHundredThirteenDG_28111, prime_oneHundredThirteenDG_1056557421397112711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860814 : Nat.totient 133596157903618934308783860814 = 66798078951807443282217820536 := by
  rw [← show ((([(2, 1), (33561636585053, 1), (1990310537524819, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_33561636585053, prime_oneHundredThirteenDG_1990310537524819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860815 : Nat.totient 133596157903618934308783860815 = 106685433863233212133157879808 := by
  rw [← show ((([(5, 1), (569, 1), (29179, 1), (33516529, 1), (48015588629297, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_569, prime_oneHundredThirteenDG_29179, prime_oneHundredThirteenDG_33516529, prime_oneHundredThirteenDG_48015588629297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860816 : Nat.totient 133596157903618934308783860816 = 43641368437565692044460984320 := by
  rw [← show ((([(2, 4), (3, 1), (53, 1), (911, 1), (17483, 1), (327825787, 1), (10057717069, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_53, prime_oneHundredThirteenDG_911, prime_oneHundredThirteenDG_17483, prime_oneHundredThirteenDG_327825787, prime_oneHundredThirteenDG_10057717069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860817 : Nat.totient 133596157903618934308783860817 = 133596157903618934308783860816 := by
  rw [← show ((([(133596157903618934308783860817, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_133596157903618934308783860817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860818 : Nat.totient 133596157903618934308783860818 = 60724030285574864822178457200 := by
  rw [← show ((([(2, 1), (11, 1), (40591, 1), (149603425192349999561909, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_11, prime_oneHundredThirteenDG_40591, prime_oneHundredThirteenDG_149603425192349999561909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860819 : Nat.totient 133596157903618934308783860819 = 89051070860569876815640638720 := by
  rw [← show ((([(3, 2), (6833, 1), (75545359207, 1), (28756249808861, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_6833, prime_oneHundredThirteenDG_75545359207, prime_oneHundredThirteenDG_28756249808861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860820 : Nat.totient 133596157903618934308783860820 = 45682804168338135297522401280 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (619, 1), (967, 1), (155461, 1), (4334593, 1), (2365805447, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_7, prime_oneHundredThirteenDG_619, prime_oneHundredThirteenDG_967, prime_oneHundredThirteenDG_155461, prime_oneHundredThirteenDG_4334593, prime_oneHundredThirteenDG_2365805447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860821 : Nat.totient 133596157903618934308783860821 = 133596157903618934308783860820 := by
  rw [← show ((([(133596157903618934308783860821, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_133596157903618934308783860821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860822 : Nat.totient 133596157903618934308783860822 = 41872996584977117709907353600 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (1061, 1), (2089357, 1), (64470941, 1), (9164351773, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_17, prime_oneHundredThirteenDG_1061, prime_oneHundredThirteenDG_2089357, prime_oneHundredThirteenDG_64470941, prime_oneHundredThirteenDG_9164351773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860823 : Nat.totient 133596157903618934308783860823 = 123275859851000384029388390400 := by
  rw [← show ((([(13, 1), (3457, 1), (20627, 1), (61231, 1), (17489149, 1), (134578331, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_13, prime_oneHundredThirteenDG_3457, prime_oneHundredThirteenDG_20627, prime_oneHundredThirteenDG_61231, prime_oneHundredThirteenDG_17489149, prime_oneHundredThirteenDG_134578331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860824 : Nat.totient 133596157903618934308783860824 = 66625763941838412335562993792 := by
  rw [← show ((([(2, 3), (389, 1), (111493, 1), (385040824561486799939, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_389, prime_oneHundredThirteenDG_111493, prime_oneHundredThirteenDG_385040824561486799939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860825 : Nat.totient 133596157903618934308783860825 = 71251284215263431631351392400 := by
  rw [← show ((([(3, 1), (5, 2), (1781282105381585790783784811, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_1781282105381585790783784811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860826 : Nat.totient 133596157903618934308783860826 = 66797936042724743257231269120 := by
  rw [← show ((([(2, 1), (650269, 1), (1755583, 1), (31806641, 1), (1839635359, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_650269, prime_oneHundredThirteenDG_1755583, prime_oneHundredThirteenDG_31806641, prime_oneHundredThirteenDG_1839635359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860827 : Nat.totient 133596157903618934308783860827 = 110541009126421640942152661376 := by
  rw [← show ((([(7, 1), (29, 1), (5189, 1), (5168279, 1), (24539646912758539, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_7, prime_oneHundredThirteenDG_29, prime_oneHundredThirteenDG_5189, prime_oneHundredThirteenDG_5168279, prime_oneHundredThirteenDG_24539646912758539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860828 : Nat.totient 133596157903618934308783860828 = 44484117163458331911930890496 := by
  rw [← show ((([(2, 2), (3, 2), (929, 1), (3994622590109404805309887, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_929, prime_oneHundredThirteenDG_3994622590109404805309887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860829 : Nat.totient 133596157903618934308783860829 = 114436682862511854892111067520 := by
  rw [← show ((([(11, 1), (23, 1), (67, 1), (1244981737, 1), (6330465756109267, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_11, prime_oneHundredThirteenDG_23, prime_oneHundredThirteenDG_67, prime_oneHundredThirteenDG_1244981737, prime_oneHundredThirteenDG_6330465756109267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860830 : Nat.totient 133596157903618934308783860830 = 50590326632428059494522132736 := by
  rw [← show ((([(2, 1), (5, 1), (19, 1), (1423, 1), (5653993, 1), (87393714970879463, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_19, prime_oneHundredThirteenDG_1423, prime_oneHundredThirteenDG_5653993, prime_oneHundredThirteenDG_87393714970879463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860831 : Nat.totient 133596157903618934308783860831 = 87991043759813274002572502552 := by
  rw [← show ((([(3, 1), (83, 1), (536530754633007768308368919, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_83, prime_oneHundredThirteenDG_536530754633007768308368919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860832 : Nat.totient 133596157903618934308783860832 = 66457240178159640071926540800 := by
  rw [← show ((([(2, 5), (331, 1), (479, 1), (12448711741, 1), (2115222571939, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_331, prime_oneHundredThirteenDG_479, prime_oneHundredThirteenDG_12448711741, prime_oneHundredThirteenDG_2115222571939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860833 : Nat.totient 133596157903618934308783860833 = 133596157903610411418988883460 := by
  rw [← show ((([(15703918998743, 1), (8507185875978631, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_15703918998743, prime_oneHundredThirteenDG_8507185875978631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860834 : Nat.totient 133596157903618934308783860834 = 37802024980441488523621908480 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (173, 1), (257, 1), (9635267, 1), (7425089584136171, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_7, prime_oneHundredThirteenDG_173, prime_oneHundredThirteenDG_257, prime_oneHundredThirteenDG_9635267, prime_oneHundredThirteenDG_7425089584136171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860835 : Nat.totient 133596157903618934308783860835 = 106876926322844594561362113984 := by
  rw [← show ((([(5, 1), (2114514524809, 1), (12636106901718863, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_2114514524809, prime_oneHundredThirteenDG_12636106901718863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860836 : Nat.totient 133596157903618934308783860836 = 60879261800316085249846020480 := by
  rw [← show ((([(2, 2), (13, 1), (79, 1), (2086253237, 1), (15588219408245191, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_13, prime_oneHundredThirteenDG_79, prime_oneHundredThirteenDG_2086253237, prime_oneHundredThirteenDG_15588219408245191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860837 : Nat.totient 133596157903618934308783860837 = 86411689149454861110223219200 := by
  rw [← show ((([(3, 3), (41, 1), (181, 1), (1553597, 1), (429170042096595463, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_41, prime_oneHundredThirteenDG_181, prime_oneHundredThirteenDG_1553597, prime_oneHundredThirteenDG_429170042096595463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860838 : Nat.totient 133596157903618934308783860838 = 66623671409226092053208372160 := by
  rw [← show ((([(2, 1), (383, 1), (2588541541, 1), (67376750221315273, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_383, prime_oneHundredThirteenDG_2588541541, prime_oneHundredThirteenDG_67376750221315273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860839 : Nat.totient 133596157903618934308783860839 = 124842750483377214007328304000 := by
  rw [← show ((([(17, 1), (151, 1), (2011, 1), (25879508806670235076147, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_17, prime_oneHundredThirteenDG_151, prime_oneHundredThirteenDG_2011, prime_oneHundredThirteenDG_25879508806670235076147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860840 : Nat.totient 133596157903618934308783860840 = 31633760085359975939054453760 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (11, 1), (43, 1), (12845453, 1), (183232352376823303, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_11, prime_oneHundredThirteenDG_43, prime_oneHundredThirteenDG_12845453, prime_oneHundredThirteenDG_183232352376823303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860841 : Nat.totient 133596157903618934308783860841 = 114505772495292308653470293760 := by
  rw [← show ((([(7, 1), (21937, 1), (804194351021, 1), (1081826648219, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_7, prime_oneHundredThirteenDG_21937, prime_oneHundredThirteenDG_804194351021, prime_oneHundredThirteenDG_1081826648219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860842 : Nat.totient 133596157903618934308783860842 = 66794860091953651529194313088 := by
  rw [← show ((([(2, 1), (20807, 1), (7863619, 1), (408255498126427937, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_20807, prime_oneHundredThirteenDG_7863619, prime_oneHundredThirteenDG_408255498126427937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860843 : Nat.totient 133596157903618934308783860843 = 86191069615238022134699265000 := by
  rw [← show ((([(3, 1), (31, 1), (1436517826920633702244987751, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_31, prime_oneHundredThirteenDG_1436517826920633702244987751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860844 : Nat.totient 133596157903618934308783860844 = 66506384255969644251364290240 := by
  rw [← show ((([(2, 2), (229, 1), (2381352331, 1), (61245592286912989, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_229, prime_oneHundredThirteenDG_2381352331, prime_oneHundredThirteenDG_61245592286912989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860845 : Nat.totient 133596157903618934308783860845 = 105412858839019871454602059776 := by
  rw [← show ((([(5, 1), (73, 1), (366016870968818998106257153, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_73, prime_oneHundredThirteenDG_366016870968818998106257153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860846 : Nat.totient 133596157903618934308783860846 = 44532052634528152586650588320 := by
  rw [← show ((([(2, 1), (3, 2), (3882857796457, 1), (1911480966208871, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_3882857796457, prime_oneHundredThirteenDG_1911480966208871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860847 : Nat.totient 133596157903618934308783860847 = 133596157794679565323665983320 := by
  rw [← show ((([(1226334971, 1), (108939368983891542557, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_1226334971, prime_oneHundredThirteenDG_108939368983891542557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860848 : Nat.totient 133596157903618934308783860848 = 57255496244408114703764511744 := by
  rw [← show ((([(2, 4), (7, 1), (1192822838425169056328427329, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_7, prime_oneHundredThirteenDG_1192822838425169056328427329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860849 : Nat.totient 133596157903618934308783860849 = 77844294272952840557127313152 := by
  rw [← show ((([(3, 1), (13, 1), (19, 1), (1867, 1), (10101659, 1), (9559578382337813, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_13, prime_oneHundredThirteenDG_19, prime_oneHundredThirteenDG_1867, prime_oneHundredThirteenDG_10101659, prime_oneHundredThirteenDG_9559578382337813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860850 : Nat.totient 133596157903618934308783860850 = 51961335028781516769416207040 := by
  rw [← show ((([(2, 1), (5, 2), (37, 1), (1583, 1), (45618534053923933109827, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_37, prime_oneHundredThirteenDG_1583, prime_oneHundredThirteenDG_45618534053923933109827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860851 : Nat.totient 133596157903618934308783860851 = 121226304959787188599439423520 := by
  rw [← show ((([(11, 1), (743, 1), (1979, 1), (8259745676824257438253, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_11, prime_oneHundredThirteenDG_743, prime_oneHundredThirteenDG_1979, prime_oneHundredThirteenDG_8259745676824257438253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860852 : Nat.totient 133596157903618934308783860852 = 42595876151005219278483710848 := by
  rw [← show ((([(2, 2), (3, 1), (23, 1), (151031693, 1), (3204917065820290589, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_23, prime_oneHundredThirteenDG_151031693, prime_oneHundredThirteenDG_3204917065820290589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860853 : Nat.totient 133596157903618934308783860853 = 131324103999462279578682187728 := by
  rw [← show ((([(59, 1), (17029, 1), (132969737470395899227523, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_59, prime_oneHundredThirteenDG_17029, prime_oneHundredThirteenDG_132969737470395899227523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860854 : Nat.totient 133596157903618934308783860854 = 66786199513973470450291908456 := by
  rw [← show ((([(2, 1), (5623, 1), (11879437835996704100016349, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_5623, prime_oneHundredThirteenDG_11879437835996704100016349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860855 : Nat.totient 133596157903618934308783860855 = 59754417492354460573744742400 := by
  rw [← show ((([(3, 2), (5, 1), (7, 1), (47, 1), (3209, 1), (919081, 1), (13827431, 1), (221268989, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_7, prime_oneHundredThirteenDG_47, prime_oneHundredThirteenDG_3209, prime_oneHundredThirteenDG_919081, prime_oneHundredThirteenDG_13827431, prime_oneHundredThirteenDG_221268989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860856 : Nat.totient 133596157903618934308783860856 = 60697471256678296595045836800 := by
  rw [← show ((([(2, 3), (17, 1), (29, 1), (17749, 1), (1908460487269387263551, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_17, prime_oneHundredThirteenDG_29, prime_oneHundredThirteenDG_17749, prime_oneHundredThirteenDG_1908460487269387263551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860857 : Nat.totient 133596157903618934308783860857 = 133596157903618934308783860856 := by
  rw [← show ((([(133596157903618934308783860857, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_133596157903618934308783860857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860858 : Nat.totient 133596157903618934308783860858 = 44532052625247424420694424816 := by
  rw [← show ((([(2, 1), (3, 1), (4792401709, 1), (4646110169657696027, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_4792401709, prime_oneHundredThirteenDG_4646110169657696027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860859 : Nat.totient 133596157903618934308783860859 = 132288613391683670883501693600 := by
  rw [← show ((([(103, 1), (12619, 1), (12824387, 1), (8014846112349101, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_103, prime_oneHundredThirteenDG_12619, prime_oneHundredThirteenDG_12824387, prime_oneHundredThirteenDG_8014846112349101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860860 : Nat.totient 133596157903618934308783860860 = 53438463161366172659342114240 := by
  rw [← show ((([(2, 2), (5, 1), (656525954741, 1), (10174476495474023, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_656525954741, prime_oneHundredThirteenDG_10174476495474023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860861 : Nat.totient 133596157903618934308783860861 = 89064019716498997468028632640 := by
  rw [← show ((([(3, 1), (1439759, 1), (3759221, 1), (8227825144249133, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_1439759, prime_oneHundredThirteenDG_3759221, prime_oneHundredThirteenDG_8227825144249133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860862 : Nat.totient 133596157903618934308783860862 = 48044945598117261117702174720 := by
  rw [← show ((([(2, 1), (7, 3), (11, 2), (13, 1), (29573, 1), (4186448439825379873, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_7, prime_oneHundredThirteenDG_11, prime_oneHundredThirteenDG_13, prime_oneHundredThirteenDG_29573, prime_oneHundredThirteenDG_4186448439825379873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860863 : Nat.totient 133596157903618934308783860863 = 133596157903618934308783860862 := by
  rw [← show ((([(133596157903618934308783860863, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_133596157903618934308783860863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860864 : Nat.totient 133596157903618934308783860864 = 43646009360189322242220134400 := by
  rw [← show ((([(2, 7), (3, 3), (61, 1), (283, 1), (35423, 1), (63214779142715531, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_61, prime_oneHundredThirteenDG_283, prime_oneHundredThirteenDG_35423, prime_oneHundredThirteenDG_63214779142715531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860865 : Nat.totient 133596157903618934308783860865 = 106853707351284698794529345520 := by
  rw [← show ((([(5, 1), (4603, 1), (5804742902612163124431191, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_4603, prime_oneHundredThirteenDG_5804742902612163124431191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860866 : Nat.totient 133596157903618934308783860866 = 66780511350658843220654958000 := by
  rw [← show ((([(2, 1), (3863, 1), (242101, 1), (71423755404771989291, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3863, prime_oneHundredThirteenDG_242101, prime_oneHundredThirteenDG_71423755404771989291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860867 : Nat.totient 133596157903618934308783860867 = 89033572493875628486896060512 := by
  rw [← show ((([(3, 1), (2917, 1), (15266387601830526146587117, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_2917, prime_oneHundredThirteenDG_15266387601830526146587117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860868 : Nat.totient 133596157903618934308783860868 = 62303090594537655181122773760 := by
  rw [← show ((([(2, 2), (19, 1), (71, 1), (709, 1), (34920125209923804580937, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_19, prime_oneHundredThirteenDG_71, prime_oneHundredThirteenDG_709, prime_oneHundredThirteenDG_34920125209923804580937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860869 : Nat.totient 133596157903618934308783860869 = 112264283189416392236816640000 := by
  rw [← show ((([(7, 1), (53, 1), (1399, 1), (19301, 1), (1732757941, 1), (7696346921, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_7, prime_oneHundredThirteenDG_53, prime_oneHundredThirteenDG_1399, prime_oneHundredThirteenDG_19301, prime_oneHundredThirteenDG_1732757941, prime_oneHundredThirteenDG_7696346921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860870 : Nat.totient 133596157903618934308783860870 = 35625535681737766400206283520 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (334793, 1), (2385404311, 1), (5576148677923, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_334793, prime_oneHundredThirteenDG_2385404311, prime_oneHundredThirteenDG_5576148677923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860871 : Nat.totient 133596157903618934308783860871 = 133357341410131330230709727520 := by
  rw [← show ((([(877, 1), (1543, 1), (98725297018439056665061, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_877, prime_oneHundredThirteenDG_1543, prime_oneHundredThirteenDG_98725297018439056665061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860872 : Nat.totient 133596157903618934308783860872 = 66185227279509416876109211200 := by
  rw [← show ((([(2, 3), (109, 1), (2620171, 1), (58471986408704023231, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_109, prime_oneHundredThirteenDG_2620171, prime_oneHundredThirteenDG_58471986408704023231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860873 : Nat.totient 133596157903618934308783860873 = 76204580989361255077390264320 := by
  rw [← show ((([(3, 2), (11, 1), (17, 1), (71955683, 1), (1103175866833115057, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_11, prime_oneHundredThirteenDG_17, prime_oneHundredThirteenDG_71955683, prime_oneHundredThirteenDG_1103175866833115057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860874 : Nat.totient 133596157903618934308783860874 = 64643300280735302881063234080 := by
  rw [← show ((([(2, 1), (31, 1), (33481913, 1), (64356440457298558579, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_31, prime_oneHundredThirteenDG_33481913, prime_oneHundredThirteenDG_64356440457298558579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860875 : Nat.totient 133596157903618934308783860875 = 93391966946679880804909056000 := by
  rw [← show ((([(5, 3), (13, 1), (23, 1), (97, 1), (65761, 1), (6551423, 1), (85533645643, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_13, prime_oneHundredThirteenDG_23, prime_oneHundredThirteenDG_97, prime_oneHundredThirteenDG_65761, prime_oneHundredThirteenDG_6551423, prime_oneHundredThirteenDG_85533645643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860876 : Nat.totient 133596157903618934308783860876 = 37907739767870896062668046336 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (149, 1), (7369, 1), (29927, 1), (14989493, 1), (3229012529, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_7, prime_oneHundredThirteenDG_149, prime_oneHundredThirteenDG_7369, prime_oneHundredThirteenDG_29927, prime_oneHundredThirteenDG_14989493, prime_oneHundredThirteenDG_3229012529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860877 : Nat.totient 133596157903618934308783860877 = 133587847004169832217286448000 := by
  rw [← show ((([(17099, 1), (268493, 1), (533123051, 1), (54583681961, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_17099, prime_oneHundredThirteenDG_268493, prime_oneHundredThirteenDG_533123051, prime_oneHundredThirteenDG_54583681961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860878 : Nat.totient 133596157903618934308783860878 = 65163629283168916075104023040 := by
  rw [← show ((([(2, 1), (41, 1), (12923, 1), (351529, 1), (358637429417089237, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_41, prime_oneHundredThirteenDG_12923, prime_oneHundredThirteenDG_351529, prime_oneHundredThirteenDG_358637429417089237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860879 : Nat.totient 133596157903618934308783860879 = 89064105269079289539189240584 := by
  rw [← show ((([(3, 1), (44532052634539644769594620293, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_44532052634539644769594620293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860880 : Nat.totient 133596157903618934308783860880 = 52939038269132095472345834496 := by
  rw [← show ((([(2, 4), (5, 1), (107, 1), (17908439767, 1), (871490090456569, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_107, prime_oneHundredThirteenDG_17908439767, prime_oneHundredThirteenDG_871490090456569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860881 : Nat.totient 133596157903618934308783860881 = 133460251334032343327798321892 := by
  rw [← show ((([(983, 1), (135906569586590980985538007, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_983, prime_oneHundredThirteenDG_135906569586590980985538007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860882 : Nat.totient 133596157903618934308783860882 = 44532051834975231359546800920 := by
  rw [← show ((([(2, 1), (3, 2), (55695391, 1), (133260735568285607839, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_55695391, prime_oneHundredThirteenDG_133260735568285607839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860883 : Nat.totient 133596157903618934308783860883 = 111847946128101533807503663680 := by
  rw [← show ((([(7, 1), (43, 1), (4706319721, 1), (94307459431144423, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_7, prime_oneHundredThirteenDG_43, prime_oneHundredThirteenDG_4706319721, prime_oneHundredThirteenDG_94307459431144423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860884 : Nat.totient 133596157903618934308783860884 = 60725526319745329759432586240 := by
  rw [← show ((([(2, 2), (11, 1), (745614003983, 1), (4072182523090817, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_11, prime_oneHundredThirteenDG_745614003983, prime_oneHundredThirteenDG_4072182523090817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860885 : Nat.totient 133596157903618934308783860885 = 68794335024902594958770180352 := by
  rw [← show ((([(3, 1), (5, 1), (29, 1), (8656727, 1), (168571499, 1), (210458679427, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_29, prime_oneHundredThirteenDG_8656727, prime_oneHundredThirteenDG_168571499, prime_oneHundredThirteenDG_210458679427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860886 : Nat.totient 133596157903618934308783860886 = 66047086686358455472005120000 := by
  rw [← show ((([(2, 1), (233, 1), (293, 1), (521, 1), (601, 1), (819257041, 1), (3814240327, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_233, prime_oneHundredThirteenDG_293, prime_oneHundredThirteenDG_521, prime_oneHundredThirteenDG_601, prime_oneHundredThirteenDG_819257041, prime_oneHundredThirteenDG_3814240327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860887 : Nat.totient 133596157903618934308783860887 = 122876182098047764605607686144 := by
  rw [← show ((([(19, 1), (37, 1), (887, 1), (953, 1), (4814503, 1), (46695030271313, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_19, prime_oneHundredThirteenDG_37, prime_oneHundredThirteenDG_887, prime_oneHundredThirteenDG_953, prime_oneHundredThirteenDG_4814503, prime_oneHundredThirteenDG_46695030271313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860888 : Nat.totient 133596157903618934308783860888 = 41082464168443158203094220800 := by
  rw [← show ((([(2, 3), (3, 1), (13, 1), (2131, 1), (8747, 1), (697637, 1), (32928147032161, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_13, prime_oneHundredThirteenDG_2131, prime_oneHundredThirteenDG_8747, prime_oneHundredThirteenDG_697637, prime_oneHundredThirteenDG_32928147032161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860889 : Nat.totient 133596157903618934308783860889 = 132494447132825254787471648256 := by
  rw [← show ((([(127, 1), (2663, 1), (395019996699060423561089, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_127, prime_oneHundredThirteenDG_2663, prime_oneHundredThirteenDG_395019996699060423561089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860890 : Nat.totient 133596157903618934308783860890 = 43104433961053806434938183680 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (17, 1), (7717, 1), (116443163, 1), (124935112703561, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_7, prime_oneHundredThirteenDG_17, prime_oneHundredThirteenDG_7717, prime_oneHundredThirteenDG_116443163, prime_oneHundredThirteenDG_124935112703561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860891 : Nat.totient 133596157903618934308783860891 = 89064105269079289539189240432 := by
  rw [← show ((([(3, 5), (549778427586909194686353337, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_549778427586909194686353337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860892 : Nat.totient 133596157903618934308783860892 = 65793221832750116912072785920 := by
  rw [← show ((([(2, 2), (89, 1), (281, 1), (6299, 1), (7457, 1), (28431639190182229, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_89, prime_oneHundredThirteenDG_281, prime_oneHundredThirteenDG_6299, prime_oneHundredThirteenDG_7457, prime_oneHundredThirteenDG_28431639190182229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860893 : Nat.totient 133596157903618934308783860893 = 133596157903618934308783860892 := by
  rw [← show ((([(133596157903618934308783860893, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_133596157903618934308783860893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860894 : Nat.totient 133596157903618934308783860894 = 44531714611764500648375877120 := by
  rw [← show ((([(2, 1), (3, 1), (131743, 1), (74017099073, 1), (2283405849691, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_131743, prime_oneHundredThirteenDG_74017099073, prime_oneHundredThirteenDG_2283405849691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860895 : Nat.totient 133596157903618934308783860895 = 97160842111715094026242192000 := by
  rw [← show ((([(5, 1), (11, 1), (13439076342389, 1), (180743154582101, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_5, prime_oneHundredThirteenDG_11, prime_oneHundredThirteenDG_13439076342389, prime_oneHundredThirteenDG_180743154582101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860896 : Nat.totient 133596157903618934308783860896 = 65402594240048051560242020352 := by
  rw [← show ((([(2, 5), (67, 1), (263, 1), (443, 1), (202109, 1), (6539807, 1), (404630977, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_67, prime_oneHundredThirteenDG_263, prime_oneHundredThirteenDG_443, prime_oneHundredThirteenDG_202109, prime_oneHundredThirteenDG_6539807, prime_oneHundredThirteenDG_404630977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860897 : Nat.totient 133596157903618934308783860897 = 76340327901820438717338042960 := by
  rw [← show ((([(3, 1), (7, 1), (228731, 1), (27813115865073973213447, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_3, prime_oneHundredThirteenDG_7, prime_oneHundredThirteenDG_228731, prime_oneHundredThirteenDG_27813115865073973213447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirteenDG_133596157903618934308783860898 : Nat.totient 133596157903618934308783860898 = 63745569139929139441193137120 := by
  rw [← show ((([(2, 1), (23, 1), (431, 1), (6738432255806462943043673, 1)] : List FactorBlock).map factorBlockValue).prod) = 133596157903618934308783860898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirteenDG_2, prime_oneHundredThirteenDG_23, prime_oneHundredThirteenDG_431, prime_oneHundredThirteenDG_6738432255806462943043673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredThirteenDG : certifiedKill 1 133596157903618934308783860796 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredThirteenDG_133596157903618934308783860797, phi_oneHundredThirteenDG_133596157903618934308783860798, phi_oneHundredThirteenDG_133596157903618934308783860799,
    phi_oneHundredThirteenDG_133596157903618934308783860800, phi_oneHundredThirteenDG_133596157903618934308783860801, phi_oneHundredThirteenDG_133596157903618934308783860802,
    phi_oneHundredThirteenDG_133596157903618934308783860803, phi_oneHundredThirteenDG_133596157903618934308783860804, phi_oneHundredThirteenDG_133596157903618934308783860805,
    phi_oneHundredThirteenDG_133596157903618934308783860806, phi_oneHundredThirteenDG_133596157903618934308783860807, phi_oneHundredThirteenDG_133596157903618934308783860808,
    phi_oneHundredThirteenDG_133596157903618934308783860809, phi_oneHundredThirteenDG_133596157903618934308783860810, phi_oneHundredThirteenDG_133596157903618934308783860811,
    phi_oneHundredThirteenDG_133596157903618934308783860812, phi_oneHundredThirteenDG_133596157903618934308783860813, phi_oneHundredThirteenDG_133596157903618934308783860814,
    phi_oneHundredThirteenDG_133596157903618934308783860815, phi_oneHundredThirteenDG_133596157903618934308783860816, phi_oneHundredThirteenDG_133596157903618934308783860817,
    phi_oneHundredThirteenDG_133596157903618934308783860818, phi_oneHundredThirteenDG_133596157903618934308783860819, phi_oneHundredThirteenDG_133596157903618934308783860820,
    phi_oneHundredThirteenDG_133596157903618934308783860821, phi_oneHundredThirteenDG_133596157903618934308783860822, phi_oneHundredThirteenDG_133596157903618934308783860823,
    phi_oneHundredThirteenDG_133596157903618934308783860824, phi_oneHundredThirteenDG_133596157903618934308783860825, phi_oneHundredThirteenDG_133596157903618934308783860826,
    phi_oneHundredThirteenDG_133596157903618934308783860827, phi_oneHundredThirteenDG_133596157903618934308783860828, phi_oneHundredThirteenDG_133596157903618934308783860829,
    phi_oneHundredThirteenDG_133596157903618934308783860830, phi_oneHundredThirteenDG_133596157903618934308783860831, phi_oneHundredThirteenDG_133596157903618934308783860832,
    phi_oneHundredThirteenDG_133596157903618934308783860833, phi_oneHundredThirteenDG_133596157903618934308783860834, phi_oneHundredThirteenDG_133596157903618934308783860835,
    phi_oneHundredThirteenDG_133596157903618934308783860836, phi_oneHundredThirteenDG_133596157903618934308783860837, phi_oneHundredThirteenDG_133596157903618934308783860838,
    phi_oneHundredThirteenDG_133596157903618934308783860839, phi_oneHundredThirteenDG_133596157903618934308783860840, phi_oneHundredThirteenDG_133596157903618934308783860841,
    phi_oneHundredThirteenDG_133596157903618934308783860842, phi_oneHundredThirteenDG_133596157903618934308783860843, phi_oneHundredThirteenDG_133596157903618934308783860844,
    phi_oneHundredThirteenDG_133596157903618934308783860845, phi_oneHundredThirteenDG_133596157903618934308783860846, phi_oneHundredThirteenDG_133596157903618934308783860847,
    phi_oneHundredThirteenDG_133596157903618934308783860848, phi_oneHundredThirteenDG_133596157903618934308783860849, phi_oneHundredThirteenDG_133596157903618934308783860850,
    phi_oneHundredThirteenDG_133596157903618934308783860851, phi_oneHundredThirteenDG_133596157903618934308783860852, phi_oneHundredThirteenDG_133596157903618934308783860853,
    phi_oneHundredThirteenDG_133596157903618934308783860854, phi_oneHundredThirteenDG_133596157903618934308783860855, phi_oneHundredThirteenDG_133596157903618934308783860856,
    phi_oneHundredThirteenDG_133596157903618934308783860857, phi_oneHundredThirteenDG_133596157903618934308783860858, phi_oneHundredThirteenDG_133596157903618934308783860859,
    phi_oneHundredThirteenDG_133596157903618934308783860860, phi_oneHundredThirteenDG_133596157903618934308783860861, phi_oneHundredThirteenDG_133596157903618934308783860862,
    phi_oneHundredThirteenDG_133596157903618934308783860863, phi_oneHundredThirteenDG_133596157903618934308783860864, phi_oneHundredThirteenDG_133596157903618934308783860865,
    phi_oneHundredThirteenDG_133596157903618934308783860866, phi_oneHundredThirteenDG_133596157903618934308783860867, phi_oneHundredThirteenDG_133596157903618934308783860868,
    phi_oneHundredThirteenDG_133596157903618934308783860869, phi_oneHundredThirteenDG_133596157903618934308783860870, phi_oneHundredThirteenDG_133596157903618934308783860871,
    phi_oneHundredThirteenDG_133596157903618934308783860872, phi_oneHundredThirteenDG_133596157903618934308783860873, phi_oneHundredThirteenDG_133596157903618934308783860874,
    phi_oneHundredThirteenDG_133596157903618934308783860875, phi_oneHundredThirteenDG_133596157903618934308783860876, phi_oneHundredThirteenDG_133596157903618934308783860877,
    phi_oneHundredThirteenDG_133596157903618934308783860878, phi_oneHundredThirteenDG_133596157903618934308783860879, phi_oneHundredThirteenDG_133596157903618934308783860880,
    phi_oneHundredThirteenDG_133596157903618934308783860881, phi_oneHundredThirteenDG_133596157903618934308783860882, phi_oneHundredThirteenDG_133596157903618934308783860883,
    phi_oneHundredThirteenDG_133596157903618934308783860884, phi_oneHundredThirteenDG_133596157903618934308783860885, phi_oneHundredThirteenDG_133596157903618934308783860886,
    phi_oneHundredThirteenDG_133596157903618934308783860887, phi_oneHundredThirteenDG_133596157903618934308783860888, phi_oneHundredThirteenDG_133596157903618934308783860889,
    phi_oneHundredThirteenDG_133596157903618934308783860890, phi_oneHundredThirteenDG_133596157903618934308783860891, phi_oneHundredThirteenDG_133596157903618934308783860892,
    phi_oneHundredThirteenDG_133596157903618934308783860893, phi_oneHundredThirteenDG_133596157903618934308783860894, phi_oneHundredThirteenDG_133596157903618934308783860895,
    phi_oneHundredThirteenDG_133596157903618934308783860896, phi_oneHundredThirteenDG_133596157903618934308783860897, phi_oneHundredThirteenDG_133596157903618934308783860898]

end TotientTailPeriodKiller
end Erdos249257
