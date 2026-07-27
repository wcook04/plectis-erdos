import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def seventyBPFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem seventyBPFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : seventyBPFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [seventyBPFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [seventyBPFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then seventyBPFastPow a n * seventyBPFastPow a n * a else seventyBPFastPow a n * seventyBPFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_seventyBP_2 : Nat.Prime 2 := by norm_num
private theorem prime_seventyBP_3 : Nat.Prime 3 := by norm_num
private theorem prime_seventyBP_5 : Nat.Prime 5 := by norm_num
private theorem prime_seventyBP_7 : Nat.Prime 7 := by norm_num
private theorem prime_seventyBP_11 : Nat.Prime 11 := by norm_num
private theorem prime_seventyBP_13 : Nat.Prime 13 := by norm_num
private theorem prime_seventyBP_17 : Nat.Prime 17 := by norm_num
private theorem prime_seventyBP_19 : Nat.Prime 19 := by norm_num
private theorem prime_seventyBP_23 : Nat.Prime 23 := by norm_num
private theorem prime_seventyBP_29 : Nat.Prime 29 := by norm_num
private theorem prime_seventyBP_31 : Nat.Prime 31 := by norm_num
private theorem prime_seventyBP_37 : Nat.Prime 37 := by norm_num
private theorem prime_seventyBP_41 : Nat.Prime 41 := by norm_num
private theorem prime_seventyBP_43 : Nat.Prime 43 := by norm_num
private theorem prime_seventyBP_47 : Nat.Prime 47 := by norm_num
private theorem prime_seventyBP_53 : Nat.Prime 53 := by norm_num
private theorem prime_seventyBP_59 : Nat.Prime 59 := by norm_num
private theorem prime_seventyBP_61 : Nat.Prime 61 := by norm_num
private theorem prime_seventyBP_67 : Nat.Prime 67 := by norm_num
private theorem prime_seventyBP_71 : Nat.Prime 71 := by norm_num
private theorem prime_seventyBP_73 : Nat.Prime 73 := by norm_num
private theorem prime_seventyBP_79 : Nat.Prime 79 := by norm_num
private theorem prime_seventyBP_83 : Nat.Prime 83 := by norm_num
private theorem prime_seventyBP_89 : Nat.Prime 89 := by norm_num
private theorem prime_seventyBP_97 : Nat.Prime 97 := by norm_num
private theorem prime_seventyBP_101 : Nat.Prime 101 := by norm_num
private theorem prime_seventyBP_103 : Nat.Prime 103 := by norm_num
private theorem prime_seventyBP_107 : Nat.Prime 107 := by norm_num
private theorem prime_seventyBP_109 : Nat.Prime 109 := by norm_num
private theorem prime_seventyBP_113 : Nat.Prime 113 := by norm_num
private theorem prime_seventyBP_127 : Nat.Prime 127 := by norm_num
private theorem prime_seventyBP_131 : Nat.Prime 131 := by norm_num
private theorem prime_seventyBP_137 : Nat.Prime 137 := by norm_num
private theorem prime_seventyBP_139 : Nat.Prime 139 := by norm_num
private theorem prime_seventyBP_149 : Nat.Prime 149 := by norm_num
private theorem prime_seventyBP_151 : Nat.Prime 151 := by norm_num
private theorem prime_seventyBP_157 : Nat.Prime 157 := by norm_num
private theorem prime_seventyBP_163 : Nat.Prime 163 := by norm_num
private theorem prime_seventyBP_167 : Nat.Prime 167 := by norm_num
private theorem prime_seventyBP_173 : Nat.Prime 173 := by norm_num
private theorem prime_seventyBP_179 : Nat.Prime 179 := by norm_num
private theorem prime_seventyBP_181 : Nat.Prime 181 := by norm_num
private theorem prime_seventyBP_191 : Nat.Prime 191 := by norm_num
private theorem prime_seventyBP_193 : Nat.Prime 193 := by norm_num
private theorem prime_seventyBP_197 : Nat.Prime 197 := by norm_num
private theorem prime_seventyBP_199 : Nat.Prime 199 := by norm_num
private theorem prime_seventyBP_211 : Nat.Prime 211 := by norm_num
private theorem prime_seventyBP_223 : Nat.Prime 223 := by norm_num
private theorem prime_seventyBP_227 : Nat.Prime 227 := by norm_num
private theorem prime_seventyBP_229 : Nat.Prime 229 := by norm_num
private theorem prime_seventyBP_233 : Nat.Prime 233 := by norm_num
private theorem prime_seventyBP_239 : Nat.Prime 239 := by norm_num
private theorem prime_seventyBP_251 : Nat.Prime 251 := by norm_num
private theorem prime_seventyBP_263 : Nat.Prime 263 := by norm_num
private theorem prime_seventyBP_269 : Nat.Prime 269 := by norm_num
private theorem prime_seventyBP_281 : Nat.Prime 281 := by norm_num
private theorem prime_seventyBP_283 : Nat.Prime 283 := by norm_num
private theorem prime_seventyBP_293 : Nat.Prime 293 := by norm_num
private theorem prime_seventyBP_307 : Nat.Prime 307 := by norm_num
private theorem prime_seventyBP_311 : Nat.Prime 311 := by norm_num
private theorem prime_seventyBP_317 : Nat.Prime 317 := by norm_num
private theorem prime_seventyBP_331 : Nat.Prime 331 := by norm_num
private theorem prime_seventyBP_337 : Nat.Prime 337 := by norm_num
private theorem prime_seventyBP_347 : Nat.Prime 347 := by norm_num
private theorem prime_seventyBP_353 : Nat.Prime 353 := by norm_num
private theorem prime_seventyBP_359 : Nat.Prime 359 := by norm_num
private theorem prime_seventyBP_367 : Nat.Prime 367 := by norm_num
private theorem prime_seventyBP_373 : Nat.Prime 373 := by norm_num
private theorem prime_seventyBP_379 : Nat.Prime 379 := by norm_num
private theorem prime_seventyBP_383 : Nat.Prime 383 := by norm_num
private theorem prime_seventyBP_389 : Nat.Prime 389 := by norm_num
private theorem prime_seventyBP_397 : Nat.Prime 397 := by norm_num
private theorem prime_seventyBP_409 : Nat.Prime 409 := by norm_num
private theorem prime_seventyBP_421 : Nat.Prime 421 := by norm_num
private theorem prime_seventyBP_431 : Nat.Prime 431 := by norm_num
private theorem prime_seventyBP_433 : Nat.Prime 433 := by norm_num
private theorem prime_seventyBP_439 : Nat.Prime 439 := by norm_num
private theorem prime_seventyBP_457 : Nat.Prime 457 := by norm_num
private theorem prime_seventyBP_461 : Nat.Prime 461 := by norm_num
private theorem prime_seventyBP_467 : Nat.Prime 467 := by norm_num
private theorem prime_seventyBP_491 : Nat.Prime 491 := by norm_num
private theorem prime_seventyBP_499 : Nat.Prime 499 := by norm_num
private theorem prime_seventyBP_521 : Nat.Prime 521 := by norm_num
private theorem prime_seventyBP_523 : Nat.Prime 523 := by norm_num
private theorem prime_seventyBP_547 : Nat.Prime 547 := by norm_num
private theorem prime_seventyBP_563 : Nat.Prime 563 := by norm_num
private theorem prime_seventyBP_569 : Nat.Prime 569 := by norm_num
private theorem prime_seventyBP_571 : Nat.Prime 571 := by norm_num
private theorem prime_seventyBP_593 : Nat.Prime 593 := by norm_num
private theorem prime_seventyBP_599 : Nat.Prime 599 := by norm_num
private theorem prime_seventyBP_607 : Nat.Prime 607 := by norm_num
private theorem prime_seventyBP_619 : Nat.Prime 619 := by norm_num
private theorem prime_seventyBP_631 : Nat.Prime 631 := by norm_num
private theorem prime_seventyBP_647 : Nat.Prime 647 := by norm_num
private theorem prime_seventyBP_653 : Nat.Prime 653 := by norm_num
private theorem prime_seventyBP_659 : Nat.Prime 659 := by norm_num
private theorem prime_seventyBP_673 : Nat.Prime 673 := by norm_num
private theorem prime_seventyBP_677 : Nat.Prime 677 := by norm_num
private theorem prime_seventyBP_709 : Nat.Prime 709 := by norm_num
private theorem prime_seventyBP_719 : Nat.Prime 719 := by norm_num
private theorem prime_seventyBP_733 : Nat.Prime 733 := by norm_num
private theorem prime_seventyBP_743 : Nat.Prime 743 := by norm_num
private theorem prime_seventyBP_769 : Nat.Prime 769 := by norm_num
private theorem prime_seventyBP_773 : Nat.Prime 773 := by norm_num
private theorem prime_seventyBP_827 : Nat.Prime 827 := by norm_num
private theorem prime_seventyBP_839 : Nat.Prime 839 := by norm_num
private theorem prime_seventyBP_853 : Nat.Prime 853 := by norm_num
private theorem prime_seventyBP_863 : Nat.Prime 863 := by norm_num
private theorem prime_seventyBP_883 : Nat.Prime 883 := by norm_num
private theorem prime_seventyBP_929 : Nat.Prime 929 := by norm_num
private theorem prime_seventyBP_937 : Nat.Prime 937 := by norm_num
private theorem prime_seventyBP_941 : Nat.Prime 941 := by norm_num
private theorem prime_seventyBP_971 : Nat.Prime 971 := by norm_num
private theorem prime_seventyBP_991 : Nat.Prime 991 := by norm_num
private theorem prime_seventyBP_997 : Nat.Prime 997 := by norm_num
private theorem prime_seventyBP_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_seventyBP_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_seventyBP_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_seventyBP_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_seventyBP_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_seventyBP_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_seventyBP_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_seventyBP_1277 : Nat.Prime 1277 := by norm_num
private theorem prime_seventyBP_1301 : Nat.Prime 1301 := by norm_num
private theorem prime_seventyBP_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_seventyBP_1319 : Nat.Prime 1319 := by norm_num
private theorem prime_seventyBP_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_seventyBP_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_seventyBP_1453 : Nat.Prime 1453 := by norm_num
private theorem prime_seventyBP_1471 : Nat.Prime 1471 := by norm_num
private theorem prime_seventyBP_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_seventyBP_1621 : Nat.Prime 1621 := by norm_num
private theorem prime_seventyBP_1627 : Nat.Prime 1627 := by norm_num
private theorem prime_seventyBP_1637 : Nat.Prime 1637 := by norm_num
private theorem prime_seventyBP_1667 : Nat.Prime 1667 := by norm_num
private theorem prime_seventyBP_1709 : Nat.Prime 1709 := by norm_num
private theorem prime_seventyBP_1741 : Nat.Prime 1741 := by norm_num
private theorem prime_seventyBP_1747 : Nat.Prime 1747 := by norm_num
private theorem prime_seventyBP_1753 : Nat.Prime 1753 := by norm_num
private theorem prime_seventyBP_2053 : Nat.Prime 2053 := by norm_num
private theorem prime_seventyBP_2069 : Nat.Prime 2069 := by norm_num
private theorem prime_seventyBP_2083 : Nat.Prime 2083 := by norm_num
private theorem prime_seventyBP_2129 : Nat.Prime 2129 := by norm_num
private theorem prime_seventyBP_2137 : Nat.Prime 2137 := by norm_num
private theorem prime_seventyBP_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_seventyBP_2297 : Nat.Prime 2297 := by norm_num
private theorem prime_seventyBP_2309 : Nat.Prime 2309 := by norm_num
private theorem prime_seventyBP_2311 : Nat.Prime 2311 := by norm_num
private theorem prime_seventyBP_2383 : Nat.Prime 2383 := by norm_num
private theorem prime_seventyBP_2437 : Nat.Prime 2437 := by norm_num
private theorem prime_seventyBP_2477 : Nat.Prime 2477 := by norm_num
private theorem prime_seventyBP_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_seventyBP_2609 : Nat.Prime 2609 := by norm_num
private theorem prime_seventyBP_2689 : Nat.Prime 2689 := by norm_num
private theorem prime_seventyBP_2753 : Nat.Prime 2753 := by norm_num
private theorem prime_seventyBP_2843 : Nat.Prime 2843 := by norm_num
private theorem prime_seventyBP_2897 : Nat.Prime 2897 := by norm_num
private theorem prime_seventyBP_2903 : Nat.Prime 2903 := by norm_num
private theorem prime_seventyBP_2927 : Nat.Prime 2927 := by norm_num
private theorem prime_seventyBP_2999 : Nat.Prime 2999 := by norm_num
private theorem prime_seventyBP_3389 : Nat.Prime 3389 := by norm_num
private theorem prime_seventyBP_3407 : Nat.Prime 3407 := by norm_num
private theorem prime_seventyBP_3517 : Nat.Prime 3517 := by norm_num
private theorem prime_seventyBP_3643 : Nat.Prime 3643 := by norm_num
private theorem prime_seventyBP_3671 : Nat.Prime 3671 := by norm_num
private theorem prime_seventyBP_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_seventyBP_3943 : Nat.Prime 3943 := by norm_num
private theorem prime_seventyBP_4001 : Nat.Prime 4001 := by norm_num
private theorem prime_seventyBP_4139 : Nat.Prime 4139 := by norm_num
private theorem prime_seventyBP_4177 : Nat.Prime 4177 := by norm_num
private theorem prime_seventyBP_4211 : Nat.Prime 4211 := by norm_num
private theorem prime_seventyBP_4219 : Nat.Prime 4219 := by norm_num
private theorem prime_seventyBP_4363 : Nat.Prime 4363 := by norm_num
private theorem prime_seventyBP_4373 : Nat.Prime 4373 := by norm_num
private theorem prime_seventyBP_4507 : Nat.Prime 4507 := by norm_num
private theorem prime_seventyBP_4759 : Nat.Prime 4759 := by norm_num
private theorem prime_seventyBP_4861 : Nat.Prime 4861 := by norm_num
private theorem prime_seventyBP_4957 : Nat.Prime 4957 := by norm_num
private theorem prime_seventyBP_4993 : Nat.Prime 4993 := by norm_num
private theorem prime_seventyBP_5279 : Nat.Prime 5279 := by norm_num
private theorem prime_seventyBP_5281 : Nat.Prime 5281 := by norm_num
private theorem prime_seventyBP_5503 : Nat.Prime 5503 := by norm_num
private theorem prime_seventyBP_5527 : Nat.Prime 5527 := by norm_num
private theorem prime_seventyBP_5647 : Nat.Prime 5647 := by norm_num
private theorem prime_seventyBP_5821 : Nat.Prime 5821 := by norm_num
private theorem prime_seventyBP_5881 : Nat.Prime 5881 := by norm_num
private theorem prime_seventyBP_5927 : Nat.Prime 5927 := by norm_num
private theorem prime_seventyBP_6151 : Nat.Prime 6151 := by norm_num
private theorem prime_seventyBP_6277 : Nat.Prime 6277 := by norm_num
private theorem prime_seventyBP_6323 : Nat.Prime 6323 := by norm_num
private theorem prime_seventyBP_6673 : Nat.Prime 6673 := by norm_num
private theorem prime_seventyBP_6689 : Nat.Prime 6689 := by norm_num
private theorem prime_seventyBP_6793 : Nat.Prime 6793 := by norm_num
private theorem prime_seventyBP_7607 : Nat.Prime 7607 := by norm_num
private theorem prime_seventyBP_7703 : Nat.Prime 7703 := by norm_num
private theorem prime_seventyBP_7741 : Nat.Prime 7741 := by norm_num
private theorem prime_seventyBP_8059 : Nat.Prime 8059 := by norm_num
private theorem prime_seventyBP_8219 : Nat.Prime 8219 := by norm_num
private theorem prime_seventyBP_8293 : Nat.Prime 8293 := by norm_num
private theorem prime_seventyBP_8573 : Nat.Prime 8573 := by norm_num
private theorem prime_seventyBP_8741 : Nat.Prime 8741 := by norm_num
private theorem prime_seventyBP_9029 : Nat.Prime 9029 := by norm_num
private theorem prime_seventyBP_9109 : Nat.Prime 9109 := by norm_num
private theorem prime_seventyBP_9281 : Nat.Prime 9281 := by norm_num
private theorem prime_seventyBP_10331 : Nat.Prime 10331 := by norm_num
private theorem prime_seventyBP_10459 : Nat.Prime 10459 := by norm_num
private theorem prime_seventyBP_10597 : Nat.Prime 10597 := by norm_num
private theorem prime_seventyBP_10729 : Nat.Prime 10729 := by norm_num
private theorem prime_seventyBP_11437 : Nat.Prime 11437 := by norm_num
private theorem prime_seventyBP_11971 : Nat.Prime 11971 := by norm_num
private theorem prime_seventyBP_12211 : Nat.Prime 12211 := by norm_num
private theorem prime_seventyBP_12263 : Nat.Prime 12263 := by norm_num
private theorem prime_seventyBP_12619 : Nat.Prime 12619 := by norm_num
private theorem prime_seventyBP_13103 : Nat.Prime 13103 := by norm_num
private theorem prime_seventyBP_13339 : Nat.Prime 13339 := by norm_num
private theorem prime_seventyBP_13397 : Nat.Prime 13397 := by norm_num
private theorem prime_seventyBP_13457 : Nat.Prime 13457 := by norm_num
private theorem prime_seventyBP_13553 : Nat.Prime 13553 := by norm_num
private theorem prime_seventyBP_14489 : Nat.Prime 14489 := by norm_num
private theorem prime_seventyBP_14621 : Nat.Prime 14621 := by norm_num
private theorem prime_seventyBP_14699 : Nat.Prime 14699 := by norm_num
private theorem prime_seventyBP_14947 : Nat.Prime 14947 := by norm_num
private theorem prime_seventyBP_15373 : Nat.Prime 15373 := by norm_num
private theorem prime_seventyBP_15461 : Nat.Prime 15461 := by norm_num
private theorem prime_seventyBP_15619 : Nat.Prime 15619 := by norm_num
private theorem prime_seventyBP_15733 : Nat.Prime 15733 := by norm_num
private theorem prime_seventyBP_15817 : Nat.Prime 15817 := by norm_num
private theorem prime_seventyBP_17189 : Nat.Prime 17189 := by norm_num
private theorem prime_seventyBP_17257 : Nat.Prime 17257 := by norm_num
private theorem prime_seventyBP_17923 : Nat.Prime 17923 := by norm_num
private theorem prime_seventyBP_17959 : Nat.Prime 17959 := by norm_num
private theorem prime_seventyBP_18097 : Nat.Prime 18097 := by norm_num
private theorem prime_seventyBP_18307 : Nat.Prime 18307 := by norm_num
private theorem prime_seventyBP_18947 : Nat.Prime 18947 := by norm_num
private theorem prime_seventyBP_19079 : Nat.Prime 19079 := by norm_num
private theorem prime_seventyBP_19301 : Nat.Prime 19301 := by norm_num
private theorem prime_seventyBP_19469 : Nat.Prime 19469 := by norm_num
private theorem prime_seventyBP_19997 : Nat.Prime 19997 := by norm_num
private theorem prime_seventyBP_21929 : Nat.Prime 21929 := by norm_num
private theorem prime_seventyBP_25301 : Nat.Prime 25301 := by norm_num
private theorem prime_seventyBP_25969 : Nat.Prime 25969 := by norm_num
private theorem prime_seventyBP_26203 : Nat.Prime 26203 := by norm_num
private theorem prime_seventyBP_27743 : Nat.Prime 27743 := by norm_num
private theorem prime_seventyBP_27893 : Nat.Prime 27893 := by norm_num
private theorem prime_seventyBP_28001 : Nat.Prime 28001 := by norm_num
private theorem prime_seventyBP_29581 : Nat.Prime 29581 := by norm_num
private theorem prime_seventyBP_30757 : Nat.Prime 30757 := by norm_num
private theorem prime_seventyBP_31307 : Nat.Prime 31307 := by norm_num
private theorem prime_seventyBP_32083 : Nat.Prime 32083 := by norm_num
private theorem prime_seventyBP_32251 : Nat.Prime 32251 := by norm_num
private theorem prime_seventyBP_32369 : Nat.Prime 32369 := by norm_num
private theorem prime_seventyBP_35251 : Nat.Prime 35251 := by norm_num
private theorem prime_seventyBP_36877 : Nat.Prime 36877 := by norm_num
private theorem prime_seventyBP_37039 : Nat.Prime 37039 := by norm_num
private theorem prime_seventyBP_39133 : Nat.Prime 39133 := by norm_num
private theorem prime_seventyBP_39667 : Nat.Prime 39667 := by norm_num
private theorem prime_seventyBP_41269 : Nat.Prime 41269 := by norm_num
private theorem prime_seventyBP_41453 : Nat.Prime 41453 := by norm_num
private theorem prime_seventyBP_41729 : Nat.Prime 41729 := by norm_num
private theorem prime_seventyBP_42157 : Nat.Prime 42157 := by norm_num
private theorem prime_seventyBP_44273 : Nat.Prime 44273 := by norm_num
private theorem prime_seventyBP_44657 : Nat.Prime 44657 := by norm_num
private theorem prime_seventyBP_45589 : Nat.Prime 45589 := by norm_num
private theorem prime_seventyBP_46457 : Nat.Prime 46457 := by norm_num
private theorem prime_seventyBP_48193 : Nat.Prime 48193 := by norm_num
private theorem prime_seventyBP_49633 : Nat.Prime 49633 := by norm_num
private theorem prime_seventyBP_51059 : Nat.Prime 51059 := by norm_num
private theorem prime_seventyBP_51343 : Nat.Prime 51343 := by norm_num
private theorem prime_seventyBP_53093 : Nat.Prime 53093 := by norm_num
private theorem prime_seventyBP_54779 : Nat.Prime 54779 := by norm_num
private theorem prime_seventyBP_55667 : Nat.Prime 55667 := by norm_num
private theorem prime_seventyBP_58477 : Nat.Prime 58477 := by norm_num
private theorem prime_seventyBP_59951 : Nat.Prime 59951 := by norm_num
private theorem prime_seventyBP_61129 : Nat.Prime 61129 := by norm_num
private theorem prime_seventyBP_61379 : Nat.Prime 61379 := by norm_num
private theorem prime_seventyBP_63073 : Nat.Prime 63073 := by norm_num
private theorem prime_seventyBP_64817 : Nat.Prime 64817 := by norm_num
private theorem prime_seventyBP_65293 : Nat.Prime 65293 := by norm_num
private theorem prime_seventyBP_69463 : Nat.Prime 69463 := by norm_num
private theorem prime_seventyBP_71711 : Nat.Prime 71711 := by norm_num
private theorem prime_seventyBP_72077 : Nat.Prime 72077 := by norm_num
private theorem prime_seventyBP_75967 : Nat.Prime 75967 := by norm_num
private theorem prime_seventyBP_80831 : Nat.Prime 80831 := by norm_num
private theorem prime_seventyBP_86311 : Nat.Prime 86311 := by norm_num
private theorem prime_seventyBP_88019 : Nat.Prime 88019 := by norm_num
private theorem prime_seventyBP_94709 : Nat.Prime 94709 := by norm_num
private theorem prime_seventyBP_101107 : Nat.Prime 101107 := by norm_num
private theorem prime_seventyBP_103079 : Nat.Prime 103079 := by norm_num
private theorem prime_seventyBP_103171 : Nat.Prime 103171 := by norm_num
private theorem prime_seventyBP_103177 : Nat.Prime 103177 := by norm_num
private theorem prime_seventyBP_112111 : Nat.Prime 112111 := by norm_num
private theorem prime_seventyBP_119027 : Nat.Prime 119027 := by norm_num
private theorem prime_seventyBP_126461 : Nat.Prime 126461 := by norm_num
private theorem prime_seventyBP_126739 : Nat.Prime 126739 := by norm_num
private theorem prime_seventyBP_129263 : Nat.Prime 129263 := by norm_num
private theorem prime_seventyBP_136603 : Nat.Prime 136603 := by norm_num
private theorem prime_seventyBP_151121 : Nat.Prime 151121 := by norm_num
private theorem prime_seventyBP_154991 : Nat.Prime 154991 := by norm_num
private theorem prime_seventyBP_166631 : Nat.Prime 166631 := by norm_num
private theorem prime_seventyBP_173473 : Nat.Prime 173473 := by norm_num
private theorem prime_seventyBP_177917 : Nat.Prime 177917 := by norm_num
private theorem prime_seventyBP_182803 : Nat.Prime 182803 := by norm_num
private theorem prime_seventyBP_183509 : Nat.Prime 183509 := by norm_num
private theorem prime_seventyBP_201281 : Nat.Prime 201281 := by norm_num
private theorem prime_seventyBP_201953 : Nat.Prime 201953 := by norm_num
private theorem prime_seventyBP_214141 : Nat.Prime 214141 := by norm_num
private theorem prime_seventyBP_229171 : Nat.Prime 229171 := by norm_num
private theorem prime_seventyBP_234571 : Nat.Prime 234571 := by norm_num
private theorem prime_seventyBP_241663 : Nat.Prime 241663 := by norm_num
private theorem prime_seventyBP_253433 : Nat.Prime 253433 := by norm_num
private theorem prime_seventyBP_260411 : Nat.Prime 260411 := by norm_num
private theorem prime_seventyBP_260677 : Nat.Prime 260677 := by norm_num
private theorem prime_seventyBP_281423 : Nat.Prime 281423 := by norm_num
private theorem prime_seventyBP_310117 : Nat.Prime 310117 := by norm_num
private theorem prime_seventyBP_311957 : Nat.Prime 311957 := by norm_num
private theorem prime_seventyBP_322079 : Nat.Prime 322079 := by norm_num
private theorem prime_seventyBP_325783 : Nat.Prime 325783 := by norm_num
private theorem prime_seventyBP_332303 : Nat.Prime 332303 := by norm_num
private theorem prime_seventyBP_332309 : Nat.Prime 332309 := by norm_num
private theorem prime_seventyBP_339067 : Nat.Prime 339067 := by norm_num
private theorem prime_seventyBP_342413 : Nat.Prime 342413 := by norm_num
private theorem prime_seventyBP_352543 : Nat.Prime 352543 := by norm_num
private theorem prime_seventyBP_361111 : Nat.Prime 361111 := by norm_num
private theorem prime_seventyBP_373211 : Nat.Prime 373211 := by norm_num
private theorem prime_seventyBP_377593 : Nat.Prime 377593 := by norm_num
private theorem prime_seventyBP_412987 : Nat.Prime 412987 := by norm_num
private theorem prime_seventyBP_427237 : Nat.Prime 427237 := by norm_num
private theorem prime_seventyBP_449971 : Nat.Prime 449971 := by norm_num
private theorem prime_seventyBP_465659 : Nat.Prime 465659 := by norm_num
private theorem prime_seventyBP_485923 : Nat.Prime 485923 := by norm_num
private theorem prime_seventyBP_490247 : Nat.Prime 490247 := by norm_num
private theorem prime_seventyBP_526667 : Nat.Prime 526667 := by norm_num
private theorem prime_seventyBP_610703 : Nat.Prime 610703 := by norm_num
private theorem prime_seventyBP_625909 : Nat.Prime 625909 := by norm_num
private theorem prime_seventyBP_630997 : Nat.Prime 630997 := by norm_num
private theorem prime_seventyBP_636017 : Nat.Prime 636017 := by norm_num
private theorem prime_seventyBP_636283 : Nat.Prime 636283 := by norm_num
private theorem prime_seventyBP_643129 : Nat.Prime 643129 := by norm_num
private theorem prime_seventyBP_660973 : Nat.Prime 660973 := by norm_num
private theorem prime_seventyBP_661093 : Nat.Prime 661093 := by norm_num
private theorem prime_seventyBP_673271 : Nat.Prime 673271 := by norm_num
private theorem prime_seventyBP_716543 : Nat.Prime 716543 := by norm_num
private theorem prime_seventyBP_724123 : Nat.Prime 724123 := by norm_num
private theorem prime_seventyBP_736441 : Nat.Prime 736441 := by norm_num
private theorem prime_seventyBP_789227 : Nat.Prime 789227 := by norm_num
private theorem prime_seventyBP_813997 : Nat.Prime 813997 := by norm_num
private theorem prime_seventyBP_826493 : Nat.Prime 826493 := by norm_num
private theorem prime_seventyBP_854999 : Nat.Prime 854999 := by norm_num
private theorem prime_seventyBP_869371 : Nat.Prime 869371 := by norm_num
private theorem prime_seventyBP_879089 : Nat.Prime 879089 := by norm_num
private theorem prime_seventyBP_884309 : Nat.Prime 884309 := by norm_num
private theorem prime_seventyBP_921203 : Nat.Prime 921203 := by norm_num
private theorem prime_seventyBP_966419 : Nat.Prime 966419 := by norm_num
private theorem prime_seventyBP_1148879 : Nat.Prime 1148879 := by norm_num
private theorem prime_seventyBP_1166141 : Nat.Prime 1166141 := by norm_num
private theorem prime_seventyBP_1214687 : Nat.Prime 1214687 := by norm_num
private theorem prime_seventyBP_1378253 : Nat.Prime 1378253 := by norm_num
private theorem prime_seventyBP_1535609 : Nat.Prime 1535609 := by norm_num
private theorem prime_seventyBP_1656101 : Nat.Prime 1656101 := by norm_num
private theorem prime_seventyBP_1687837 : Nat.Prime 1687837 := by norm_num
private theorem prime_seventyBP_1707919 : Nat.Prime 1707919 := by norm_num
private theorem prime_seventyBP_1728253 : Nat.Prime 1728253 := by norm_num
private theorem prime_seventyBP_1820153 : Nat.Prime 1820153 := by norm_num
private theorem prime_seventyBP_1823729 : Nat.Prime 1823729 := by norm_num
private theorem prime_seventyBP_2021009 : Nat.Prime 2021009 := by norm_num
private theorem prime_seventyBP_2042767 : Nat.Prime 2042767 := by norm_num
private theorem prime_seventyBP_2156849 : Nat.Prime 2156849 := by norm_num
private theorem prime_seventyBP_2174077 : Nat.Prime 2174077 := by norm_num
private theorem prime_seventyBP_2177281 : Nat.Prime 2177281 := by norm_num
private theorem prime_seventyBP_2359213 : Nat.Prime 2359213 := by norm_num
private theorem prime_seventyBP_2454493 : Nat.Prime 2454493 := by norm_num
private theorem prime_seventyBP_2557631 : Nat.Prime 2557631 := by norm_num
private theorem prime_seventyBP_2632151 : Nat.Prime 2632151 := by norm_num
private theorem prime_seventyBP_2932151 : Nat.Prime 2932151 := by norm_num
private theorem prime_seventyBP_3088873 : Nat.Prime 3088873 := by norm_num
private theorem prime_seventyBP_3110027 : Nat.Prime 3110027 := by norm_num
private theorem prime_seventyBP_3110369 : Nat.Prime 3110369 := by norm_num
private theorem prime_seventyBP_3308867 : Nat.Prime 3308867 := by norm_num
private theorem prime_seventyBP_3356593 : Nat.Prime 3356593 := by norm_num
private theorem prime_seventyBP_3369397 : Nat.Prime 3369397 := by norm_num
private theorem prime_seventyBP_3549307 : Nat.Prime 3549307 := by norm_num
private theorem prime_seventyBP_3607237 : Nat.Prime 3607237 := by norm_num
private theorem prime_seventyBP_3711943 : Nat.Prime 3711943 := by norm_num
private theorem prime_seventyBP_3738607 : Nat.Prime 3738607 := by norm_num
private theorem prime_seventyBP_4046239 : Nat.Prime 4046239 := by norm_num
private theorem prime_seventyBP_4144711 : Nat.Prime 4144711 := by norm_num
private theorem prime_seventyBP_4206337 : Nat.Prime 4206337 := by norm_num
private theorem prime_seventyBP_4247629 : Nat.Prime 4247629 := by norm_num
private theorem prime_seventyBP_4357807 : Nat.Prime 4357807 := by norm_num
private theorem prime_seventyBP_4424921 : Nat.Prime 4424921 := by norm_num
private theorem prime_seventyBP_4426117 : Nat.Prime 4426117 := by norm_num
private theorem prime_seventyBP_4438507 : Nat.Prime 4438507 := by norm_num
private theorem prime_seventyBP_4514641 : Nat.Prime 4514641 := by norm_num
private theorem prime_seventyBP_4528313 : Nat.Prime 4528313 := by norm_num
private theorem prime_seventyBP_4974649 : Nat.Prime 4974649 := by norm_num
private theorem prime_seventyBP_6103943 : Nat.Prime 6103943 := by norm_num
private theorem prime_seventyBP_6164813 : Nat.Prime 6164813 := by norm_num
private theorem prime_seventyBP_6323003 : Nat.Prime 6323003 := by norm_num
private theorem prime_seventyBP_6971389 : Nat.Prime 6971389 := by norm_num
private theorem prime_seventyBP_7266071 : Nat.Prime 7266071 := by norm_num
private theorem prime_seventyBP_7853561 : Nat.Prime 7853561 := by norm_num
private theorem prime_seventyBP_8646221 : Nat.Prime 8646221 := by norm_num
private theorem prime_seventyBP_8663621 : Nat.Prime 8663621 := by norm_num
private theorem prime_seventyBP_8887871 : Nat.Prime 8887871 := by norm_num
private theorem prime_seventyBP_9237929 : Nat.Prime 9237929 := by norm_num
private theorem prime_seventyBP_9597079 : Nat.Prime 9597079 := by norm_num
private theorem prime_seventyBP_11357393 : Nat.Prime 11357393 := by norm_num
private theorem prime_seventyBP_13637797 : Nat.Prime 13637797 := by norm_num
private theorem prime_seventyBP_13711771 : Nat.Prime 13711771 := by norm_num
private theorem prime_seventyBP_13793777 : Nat.Prime 13793777 := by norm_num
private theorem prime_seventyBP_14298077 : Nat.Prime 14298077 := by norm_num
private theorem prime_seventyBP_15021131 : Nat.Prime 15021131 := by norm_num
private theorem prime_seventyBP_15622273 : Nat.Prime 15622273 := by norm_num
private theorem prime_seventyBP_15654523 : Nat.Prime 15654523 := by norm_num
private theorem prime_seventyBP_16852349 : Nat.Prime 16852349 := by norm_num
private theorem prime_seventyBP_17752279 : Nat.Prime 17752279 := by norm_num
private theorem prime_seventyBP_18226121 : Nat.Prime 18226121 := by norm_num
private theorem prime_seventyBP_18420209 : Nat.Prime 18420209 := by norm_num
private theorem prime_seventyBP_19129889 : Nat.Prime 19129889 := by norm_num
private theorem prime_seventyBP_20349389 : Nat.Prime 20349389 := by norm_num
private theorem prime_seventyBP_20532157 : Nat.Prime 20532157 := by norm_num
private theorem prime_seventyBP_21130397 : Nat.Prime 21130397 := by norm_num
private theorem prime_seventyBP_21613019 : Nat.Prime 21613019 := by norm_num
private theorem prime_seventyBP_22332481 : Nat.Prime 22332481 := by norm_num
private theorem prime_seventyBP_22586261 : Nat.Prime 22586261 := by norm_num
private theorem prime_seventyBP_23210071 : Nat.Prime 23210071 := by norm_num
private theorem prime_seventyBP_25246811 : Nat.Prime 25246811 := by norm_num
private theorem prime_seventyBP_26035441 : Nat.Prime 26035441 := by norm_num
private theorem prime_seventyBP_26919103 : Nat.Prime 26919103 := by norm_num
private theorem prime_seventyBP_26937011 : Nat.Prime 26937011 := by norm_num
private theorem prime_seventyBP_28722817 : Nat.Prime 28722817 := by norm_num
private theorem prime_seventyBP_30463957 : Nat.Prime 30463957 := by
  apply lucas_primality 30463957 (6 : ZMod 30463957)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (409, 1), (2069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (409, 1), (2069, 1)] : List FactorBlock).map factorBlockValue).prod) = 30463957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_409
      · exact prime_seventyBP_2069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 30463957) ^ 15231978 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 30463957) ^ 10154652 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 30463957) ^ 74484 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 30463957) ^ 14724 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_31104473 : Nat.Prime 31104473 := by
  apply lucas_primality 31104473 (5 : ZMod 31104473)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (29, 1), (107, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (29, 1), (107, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) = 31104473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_29
      · exact prime_seventyBP_107
      · exact prime_seventyBP_179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 31104473) ^ 15552236 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 31104473) ^ 4443496 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 31104473) ^ 1072568 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 31104473) ^ 290696 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 31104473) ^ 173768 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_31672009 : Nat.Prime 31672009 := by
  apply lucas_primality 31672009 (7 : ZMod 31672009)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (41, 1), (10729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (41, 1), (10729, 1)] : List FactorBlock).map factorBlockValue).prod) = 31672009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_41
      · exact prime_seventyBP_10729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 31672009) ^ 15836004 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 31672009) ^ 10557336 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 31672009) ^ 772488 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 31672009) ^ 2952 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_35701493 : Nat.Prime 35701493 := by
  apply lucas_primality 35701493 (2 : ZMod 35701493)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1153, 1), (7741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1153, 1), (7741, 1)] : List FactorBlock).map factorBlockValue).prod) = 35701493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_1153
      · exact prime_seventyBP_7741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35701493) ^ 17850746 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35701493) ^ 30964 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35701493) ^ 4612 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_37799059 : Nat.Prime 37799059 := by
  apply lucas_primality 37799059 (2 : ZMod 37799059)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (59, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (59, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) = 37799059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_11
      · exact prime_seventyBP_17
      · exact prime_seventyBP_59
      · exact prime_seventyBP_571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37799059) ^ 18899529 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37799059) ^ 12599686 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37799059) ^ 3436278 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37799059) ^ 2223474 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37799059) ^ 640662 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37799059) ^ 66198 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_38666081 : Nat.Prime 38666081 := by
  apply lucas_primality 38666081 (3 : ZMod 38666081)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (241663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (241663, 1)] : List FactorBlock).map factorBlockValue).prod) = 38666081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_241663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 38666081) ^ 19333040 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 38666081) ^ 7733216 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 38666081) ^ 160 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_40589599 : Nat.Prime 40589599 := by
  apply lucas_primality 40589599 (3 : ZMod 40589599)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (966419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (966419, 1)] : List FactorBlock).map factorBlockValue).prod) = 40589599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_7
      · exact prime_seventyBP_966419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 40589599) ^ 20294799 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 40589599) ^ 13529866 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 40589599) ^ 5798514 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 40589599) ^ 42 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_45146411 : Nat.Prime 45146411 := by
  apply lucas_primality 45146411 (2 : ZMod 45146411)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4514641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4514641, 1)] : List FactorBlock).map factorBlockValue).prod) = 45146411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_4514641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45146411) ^ 22573205 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 45146411) ^ 9029282 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 45146411) ^ 10 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_46068271 : Nat.Prime 46068271 := by
  apply lucas_primality 46068271 (3 : ZMod 46068271)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1535609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1535609, 1)] : List FactorBlock).map factorBlockValue).prod) = 46068271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_1535609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 46068271) ^ 23034135 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 46068271) ^ 15356090 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 46068271) ^ 9213654 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 46068271) ^ 30 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_47900183 : Nat.Prime 47900183 := by
  apply lucas_primality 47900183 (7 : ZMod 47900183)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2177281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2177281, 1)] : List FactorBlock).map factorBlockValue).prod) = 47900183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_11
      · exact prime_seventyBP_2177281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 47900183) ^ 23950091 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 47900183) ^ 4354562 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 47900183) ^ 22 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_49332431 : Nat.Prime 49332431 := by
  apply lucas_primality 49332431 (11 : ZMod 49332431)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (41, 1), (17189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (41, 1), (17189, 1)] : List FactorBlock).map factorBlockValue).prod) = 49332431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_7
      · exact prime_seventyBP_41
      · exact prime_seventyBP_17189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 49332431) ^ 24666215 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 49332431) ^ 9866486 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 49332431) ^ 7047490 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 49332431) ^ 1203230 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 49332431) ^ 2870 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_49746491 : Nat.Prime 49746491 := by
  apply lucas_primality 49746491 (6 : ZMod 49746491)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4974649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4974649, 1)] : List FactorBlock).map factorBlockValue).prod) = 49746491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_4974649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 49746491) ^ 24873245 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 49746491) ^ 9949298 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 49746491) ^ 10 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_54583229 : Nat.Prime 54583229 := by
  apply lucas_primality 54583229 (2 : ZMod 54583229)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (101, 1), (19301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (101, 1), (19301, 1)] : List FactorBlock).map factorBlockValue).prod) = 54583229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_101
      · exact prime_seventyBP_19301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 54583229) ^ 27291614 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 54583229) ^ 7797604 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 54583229) ^ 540428 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 54583229) ^ 2828 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_62208947 : Nat.Prime 62208947 := by
  apply lucas_primality 62208947 (2 : ZMod 62208947)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31104473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31104473, 1)] : List FactorBlock).map factorBlockValue).prod) = 62208947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_31104473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 62208947) ^ 31104473 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 62208947) ^ 2 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_68594249 : Nat.Prime 68594249 := by
  apply lucas_primality 68594249 (3 : ZMod 68594249)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (167, 1), (51343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (167, 1), (51343, 1)] : List FactorBlock).map factorBlockValue).prod) = 68594249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_167
      · exact prime_seventyBP_51343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68594249) ^ 34297124 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 68594249) ^ 410744 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 68594249) ^ 1336 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_73733381 : Nat.Prime 73733381 := by
  apply lucas_primality 73733381 (2 : ZMod 73733381)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (526667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (526667, 1)] : List FactorBlock).map factorBlockValue).prod) = 73733381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_7
      · exact prime_seventyBP_526667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 73733381) ^ 36866690 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 73733381) ^ 14746676 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 73733381) ^ 10533340 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 73733381) ^ 140 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_81533531 : Nat.Prime 81533531 := by
  apply lucas_primality 81533531 (2 : ZMod 81533531)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (17, 1), (79, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (17, 1), (79, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) = 81533531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_13
      · exact prime_seventyBP_17
      · exact prime_seventyBP_79
      · exact prime_seventyBP_467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 81533531) ^ 40766765 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 81533531) ^ 16306706 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 81533531) ^ 6271810 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 81533531) ^ 4796090 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 81533531) ^ 1032070 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 81533531) ^ 174590 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_81826783 : Nat.Prime 81826783 := by
  apply lucas_primality 81826783 (3 : ZMod 81826783)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13637797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13637797, 1)] : List FactorBlock).map factorBlockValue).prod) = 81826783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_13637797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 81826783) ^ 40913391 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 81826783) ^ 27275594 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 81826783) ^ 6 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_83722757 : Nat.Prime 83722757 := by
  apply lucas_primality 83722757 (2 : ZMod 83722757)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (17, 1), (94709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (17, 1), (94709, 1)] : List FactorBlock).map factorBlockValue).prod) = 83722757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_13
      · exact prime_seventyBP_17
      · exact prime_seventyBP_94709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 83722757) ^ 41861378 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 83722757) ^ 6440212 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 83722757) ^ 4924868 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 83722757) ^ 884 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_86579093 : Nat.Prime 86579093 := by
  apply lucas_primality 86579093 (2 : ZMod 86579093)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (773, 1), (28001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (773, 1), (28001, 1)] : List FactorBlock).map factorBlockValue).prod) = 86579093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_773
      · exact prime_seventyBP_28001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 86579093) ^ 43289546 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 86579093) ^ 112004 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 86579093) ^ 3092 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_93992141 : Nat.Prime 93992141 := by
  apply lucas_primality 93992141 (2 : ZMod 93992141)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (427237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (427237, 1)] : List FactorBlock).map factorBlockValue).prod) = 93992141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_11
      · exact prime_seventyBP_427237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 93992141) ^ 46996070 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 93992141) ^ 18798428 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 93992141) ^ 8544740 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 93992141) ^ 220 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_96112957 : Nat.Prime 96112957 := by
  apply lucas_primality 96112957 (2 : ZMod 96112957)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (151121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (151121, 1)] : List FactorBlock).map factorBlockValue).prod) = 96112957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_53
      · exact prime_seventyBP_151121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 96112957) ^ 48056478 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 96112957) ^ 32037652 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 96112957) ^ 1813452 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 96112957) ^ 636 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_104821531 : Nat.Prime 104821531 := by
  apply lucas_primality 104821531 (2 : ZMod 104821531)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (43, 1), (83, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (43, 1), (83, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) = 104821531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_11
      · exact prime_seventyBP_43
      · exact prime_seventyBP_83
      · exact prime_seventyBP_89
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 104821531) ^ 52410765 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 104821531) ^ 34940510 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 104821531) ^ 20964306 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 104821531) ^ 9529230 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 104821531) ^ 2437710 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 104821531) ^ 1262910 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 104821531) ^ 1177770 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_117846019 : Nat.Prime 117846019 := by
  apply lucas_primality 117846019 (3 : ZMod 117846019)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (317, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (317, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) = 117846019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_19
      · exact prime_seventyBP_317
      · exact prime_seventyBP_1087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 117846019) ^ 58923009 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 117846019) ^ 39282006 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 117846019) ^ 6202422 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 117846019) ^ 371754 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 117846019) ^ 108414 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_129463489 : Nat.Prime 129463489 := by
  apply lucas_primality 129463489 (17 : ZMod 129463489)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (7, 2), (11, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (7, 2), (11, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) = 129463489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_7
      · exact prime_seventyBP_11
      · exact prime_seventyBP_139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 129463489) ^ 64731744 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (17 : ZMod 129463489) ^ 43154496 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (17 : ZMod 129463489) ^ 18494784 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (17 : ZMod 129463489) ^ 11769408 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (17 : ZMod 129463489) ^ 931392 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_135415327 : Nat.Prime 135415327 := by
  apply lucas_primality 135415327 (5 : ZMod 135415327)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (157, 1), (4957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (157, 1), (4957, 1)] : List FactorBlock).map factorBlockValue).prod) = 135415327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_29
      · exact prime_seventyBP_157
      · exact prime_seventyBP_4957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 135415327) ^ 67707663 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 135415327) ^ 45138442 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 135415327) ^ 4669494 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 135415327) ^ 862518 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 135415327) ^ 27318 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_140027099 : Nat.Prime 140027099 := by
  apply lucas_primality 140027099 (2 : ZMod 140027099)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (383, 1), (182803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (383, 1), (182803, 1)] : List FactorBlock).map factorBlockValue).prod) = 140027099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_383
      · exact prime_seventyBP_182803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 140027099) ^ 70013549 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 140027099) ^ 365606 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 140027099) ^ 766 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_143015459 : Nat.Prime 143015459 := by
  apply lucas_primality 143015459 (2 : ZMod 143015459)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (4206337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (4206337, 1)] : List FactorBlock).map factorBlockValue).prod) = 143015459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_17
      · exact prime_seventyBP_4206337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 143015459) ^ 71507729 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 143015459) ^ 8412674 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 143015459) ^ 34 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_169873817 : Nat.Prime 169873817 := by
  apply lucas_primality 169873817 (3 : ZMod 169873817)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (719, 1), (4219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (719, 1), (4219, 1)] : List FactorBlock).map factorBlockValue).prod) = 169873817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_719
      · exact prime_seventyBP_4219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 169873817) ^ 84936908 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 169873817) ^ 24267688 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 169873817) ^ 236264 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 169873817) ^ 40264 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_169905161 : Nat.Prime 169905161 := by
  apply lucas_primality 169905161 (3 : ZMod 169905161)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (4247629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (4247629, 1)] : List FactorBlock).map factorBlockValue).prod) = 169905161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_4247629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 169905161) ^ 84952580 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 169905161) ^ 33981032 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 169905161) ^ 40 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_185345233 : Nat.Prime 185345233 := by
  apply lucas_primality 185345233 (7 : ZMod 185345233)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (883, 1), (4373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (883, 1), (4373, 1)] : List FactorBlock).map factorBlockValue).prod) = 185345233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_883
      · exact prime_seventyBP_4373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 185345233) ^ 92672616 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 185345233) ^ 61781744 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 185345233) ^ 209904 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 185345233) ^ 42384 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_205213453 : Nat.Prime 205213453 := by
  apply lucas_primality 205213453 (2 : ZMod 205213453)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (23, 1), (39133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (23, 1), (39133, 1)] : List FactorBlock).map factorBlockValue).prod) = 205213453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_19
      · exact prime_seventyBP_23
      · exact prime_seventyBP_39133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 205213453) ^ 102606726 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 205213453) ^ 68404484 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 205213453) ^ 10800708 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 205213453) ^ 8922324 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 205213453) ^ 5244 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_208828793 : Nat.Prime 208828793 := by
  apply lucas_primality 208828793 (3 : ZMod 208828793)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (103, 1), (253433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (103, 1), (253433, 1)] : List FactorBlock).map factorBlockValue).prod) = 208828793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_103
      · exact prime_seventyBP_253433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 208828793) ^ 104414396 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 208828793) ^ 2027464 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 208828793) ^ 824 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_212105071 : Nat.Prime 212105071 := by
  apply lucas_primality 212105071 (3 : ZMod 212105071)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (193, 1), (12211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (193, 1), (12211, 1)] : List FactorBlock).map factorBlockValue).prod) = 212105071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_193
      · exact prime_seventyBP_12211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 212105071) ^ 106052535 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 212105071) ^ 70701690 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 212105071) ^ 42421014 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 212105071) ^ 1098990 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 212105071) ^ 17370 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_228966121 : Nat.Prime 228966121 := by
  apply lucas_primality 228966121 (7 : ZMod 228966121)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (636017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (636017, 1)] : List FactorBlock).map factorBlockValue).prod) = 228966121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_636017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 228966121) ^ 114483060 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 228966121) ^ 76322040 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 228966121) ^ 45793224 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 228966121) ^ 360 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_229855357 : Nat.Prime 229855357 := by
  apply lucas_primality 229855357 (2 : ZMod 229855357)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2129, 1), (2999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2129, 1), (2999, 1)] : List FactorBlock).map factorBlockValue).prod) = 229855357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_2129
      · exact prime_seventyBP_2999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 229855357) ^ 114927678 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 229855357) ^ 76618452 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 229855357) ^ 107964 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 229855357) ^ 76644 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_232003769 : Nat.Prime 232003769 := by
  apply lucas_primality 232003769 (3 : ZMod 232003769)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (163, 1), (177917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (163, 1), (177917, 1)] : List FactorBlock).map factorBlockValue).prod) = 232003769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_163
      · exact prime_seventyBP_177917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 232003769) ^ 116001884 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 232003769) ^ 1423336 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 232003769) ^ 1304 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_233278897 : Nat.Prime 233278897 := by
  apply lucas_primality 233278897 (10 : ZMod 233278897)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (263, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (263, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) = 233278897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_17
      · exact prime_seventyBP_263
      · exact prime_seventyBP_1087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 233278897) ^ 116639448 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 233278897) ^ 77759632 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 233278897) ^ 13722288 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 233278897) ^ 886992 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 233278897) ^ 214608 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_248186929 : Nat.Prime 248186929 := by
  apply lucas_primality 248186929 (31 : ZMod 248186929)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (23, 1), (107, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (23, 1), (107, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) = 248186929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_11
      · exact prime_seventyBP_23
      · exact prime_seventyBP_107
      · exact prime_seventyBP_191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 248186929) ^ 124093464 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (31 : ZMod 248186929) ^ 82728976 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (31 : ZMod 248186929) ^ 22562448 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (31 : ZMod 248186929) ^ 10790736 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (31 : ZMod 248186929) ^ 2319504 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (31 : ZMod 248186929) ^ 1299408 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_298505093 : Nat.Prime 298505093 := by
  apply lucas_primality 298505093 (2 : ZMod 298505093)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (1820153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (1820153, 1)] : List FactorBlock).map factorBlockValue).prod) = 298505093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_41
      · exact prime_seventyBP_1820153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 298505093) ^ 149252546 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 298505093) ^ 7280612 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 298505093) ^ 164 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_303342283 : Nat.Prime 303342283 := by
  apply lucas_primality 303342283 (2 : ZMod 303342283)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (16852349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (16852349, 1)] : List FactorBlock).map factorBlockValue).prod) = 303342283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_16852349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 303342283) ^ 151671141 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 303342283) ^ 101114094 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 303342283) ^ 18 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_327307133 : Nat.Prime 327307133 := by
  apply lucas_primality 327307133 (2 : ZMod 327307133)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (81826783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (81826783, 1)] : List FactorBlock).map factorBlockValue).prod) = 327307133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_81826783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 327307133) ^ 163653566 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 327307133) ^ 4 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_337476011 : Nat.Prime 337476011 := by
  apply lucas_primality 337476011 (2 : ZMod 337476011)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (23, 1), (86311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (23, 1), (86311, 1)] : List FactorBlock).map factorBlockValue).prod) = 337476011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_17
      · exact prime_seventyBP_23
      · exact prime_seventyBP_86311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 337476011) ^ 168738005 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 337476011) ^ 67495202 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 337476011) ^ 19851530 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 337476011) ^ 14672870 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 337476011) ^ 3910 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_352737487 : Nat.Prime 352737487 := by
  apply lucas_primality 352737487 (3 : ZMod 352737487)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1637, 1), (11971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1637, 1), (11971, 1)] : List FactorBlock).map factorBlockValue).prod) = 352737487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_1637
      · exact prime_seventyBP_11971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 352737487) ^ 176368743 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 352737487) ^ 117579162 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 352737487) ^ 215478 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 352737487) ^ 29466 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_460633253 : Nat.Prime 460633253 := by
  apply lucas_primality 460633253 (2 : ZMod 460633253)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (743, 1), (154991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (743, 1), (154991, 1)] : List FactorBlock).map factorBlockValue).prod) = 460633253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_743
      · exact prime_seventyBP_154991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 460633253) ^ 230316626 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 460633253) ^ 619964 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 460633253) ^ 2972 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_483333943 : Nat.Prime 483333943 := by
  apply lucas_primality 483333943 (3 : ZMod 483333943)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (13, 1), (126461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (13, 1), (126461, 1)] : List FactorBlock).map factorBlockValue).prod) = 483333943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_7
      · exact prime_seventyBP_13
      · exact prime_seventyBP_126461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 483333943) ^ 241666971 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 483333943) ^ 161111314 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 483333943) ^ 69047706 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 483333943) ^ 37179534 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 483333943) ^ 3822 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_492794717 : Nat.Prime 492794717 := by
  apply lucas_primality 492794717 (2 : ZMod 492794717)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (1033, 1), (6277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (1033, 1), (6277, 1)] : List FactorBlock).map factorBlockValue).prod) = 492794717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_19
      · exact prime_seventyBP_1033
      · exact prime_seventyBP_6277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 492794717) ^ 246397358 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 492794717) ^ 25936564 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 492794717) ^ 477052 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 492794717) ^ 78508 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_547060201 : Nat.Prime 547060201 := by
  apply lucas_primality 547060201 (17 : ZMod 547060201)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (61, 1), (14947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (61, 1), (14947, 1)] : List FactorBlock).map factorBlockValue).prod) = 547060201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_61
      · exact prime_seventyBP_14947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 547060201) ^ 273530100 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (17 : ZMod 547060201) ^ 182353400 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (17 : ZMod 547060201) ^ 109412040 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (17 : ZMod 547060201) ^ 8968200 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (17 : ZMod 547060201) ^ 36600 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_557583919 : Nat.Prime 557583919 := by
  apply lucas_primality 557583919 (3 : ZMod 557583919)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (19, 1), (31, 1), (9281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (19, 1), (31, 1), (9281, 1)] : List FactorBlock).map factorBlockValue).prod) = 557583919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_17
      · exact prime_seventyBP_19
      · exact prime_seventyBP_31
      · exact prime_seventyBP_9281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 557583919) ^ 278791959 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 557583919) ^ 185861306 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 557583919) ^ 32799054 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 557583919) ^ 29346522 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 557583919) ^ 17986578 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 557583919) ^ 60078 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_589439437 : Nat.Prime 589439437 := by
  apply lucas_primality 589439437 (5 : ZMod 589439437)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (433, 1), (6673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (433, 1), (6673, 1)] : List FactorBlock).map factorBlockValue).prod) = 589439437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_17
      · exact prime_seventyBP_433
      · exact prime_seventyBP_6673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 589439437) ^ 294719718 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 589439437) ^ 196479812 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 589439437) ^ 34672908 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 589439437) ^ 1361292 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 589439437) ^ 88332 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_597010187 : Nat.Prime 597010187 := by
  apply lucas_primality 597010187 (2 : ZMod 597010187)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (298505093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (298505093, 1)] : List FactorBlock).map factorBlockValue).prod) = 597010187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_298505093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 597010187) ^ 298505093 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 597010187) ^ 2 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_615226291 : Nat.Prime 615226291 := by
  apply lucas_primality 615226291 (7 : ZMod 615226291)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (743, 1), (3943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (743, 1), (3943, 1)] : List FactorBlock).map factorBlockValue).prod) = 615226291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_7
      · exact prime_seventyBP_743
      · exact prime_seventyBP_3943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 615226291) ^ 307613145 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 615226291) ^ 205075430 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 615226291) ^ 123045258 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 615226291) ^ 87889470 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 615226291) ^ 828030 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 615226291) ^ 156030 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_650517619 : Nat.Prime 650517619 := by
  apply lucas_primality 650517619 (2 : ZMod 650517619)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (3738607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (3738607, 1)] : List FactorBlock).map factorBlockValue).prod) = 650517619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_29
      · exact prime_seventyBP_3738607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 650517619) ^ 325258809 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 650517619) ^ 216839206 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 650517619) ^ 22431642 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 650517619) ^ 174 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_662200267 : Nat.Prime 662200267 := by
  apply lucas_primality 662200267 (2 : ZMod 662200267)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (41, 1), (29581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (41, 1), (29581, 1)] : List FactorBlock).map factorBlockValue).prod) = 662200267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_7
      · exact prime_seventyBP_13
      · exact prime_seventyBP_41
      · exact prime_seventyBP_29581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 662200267) ^ 331100133 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 662200267) ^ 220733422 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 662200267) ^ 94600038 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 662200267) ^ 50938482 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 662200267) ^ 16151226 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 662200267) ^ 22386 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_736662287 : Nat.Prime 736662287 := by
  apply lucas_primality 736662287 (5 : ZMod 736662287)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (353, 1), (10331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (353, 1), (10331, 1)] : List FactorBlock).map factorBlockValue).prod) = 736662287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_101
      · exact prime_seventyBP_353
      · exact prime_seventyBP_10331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 736662287) ^ 368331143 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 736662287) ^ 7293686 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 736662287) ^ 2086862 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 736662287) ^ 71306 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_752567099 : Nat.Prime 752567099 := by
  apply lucas_primality 752567099 (2 : ZMod 752567099)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (607, 1), (19997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (607, 1), (19997, 1)] : List FactorBlock).map factorBlockValue).prod) = 752567099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_31
      · exact prime_seventyBP_607
      · exact prime_seventyBP_19997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 752567099) ^ 376283549 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 752567099) ^ 24276358 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 752567099) ^ 1239814 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 752567099) ^ 37634 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_794936339 : Nat.Prime 794936339 := by
  apply lucas_primality 794936339 (2 : ZMod 794936339)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (971, 1), (58477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (971, 1), (58477, 1)] : List FactorBlock).map factorBlockValue).prod) = 794936339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_971
      · exact prime_seventyBP_58477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 794936339) ^ 397468169 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 794936339) ^ 113562334 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 794936339) ^ 818678 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 794936339) ^ 13594 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_937369787 : Nat.Prime 937369787 := by
  apply lucas_primality 937369787 (2 : ZMod 937369787)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (73, 1), (136603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (73, 1), (136603, 1)] : List FactorBlock).map factorBlockValue).prod) = 937369787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_47
      · exact prime_seventyBP_73
      · exact prime_seventyBP_136603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 937369787) ^ 468684893 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 937369787) ^ 19944038 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 937369787) ^ 12840682 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 937369787) ^ 6862 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_980231429 : Nat.Prime 980231429 := by
  apply lucas_primality 980231429 (3 : ZMod 980231429)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (59, 1), (377593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (59, 1), (377593, 1)] : List FactorBlock).map factorBlockValue).prod) = 980231429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_11
      · exact prime_seventyBP_59
      · exact prime_seventyBP_377593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 980231429) ^ 490115714 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 980231429) ^ 89111948 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 980231429) ^ 16614092 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 980231429) ^ 2596 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_988182893 : Nat.Prime 988182893 := by
  apply lucas_primality 988182893 (2 : ZMod 988182893)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (15619, 1), (15817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (15619, 1), (15817, 1)] : List FactorBlock).map factorBlockValue).prod) = 988182893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_15619
      · exact prime_seventyBP_15817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 988182893) ^ 494091446 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 988182893) ^ 63268 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 988182893) ^ 62476 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_989548687 : Nat.Prime 989548687 := by
  apply lucas_primality 989548687 (5 : ZMod 989548687)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (7853561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (7853561, 1)] : List FactorBlock).map factorBlockValue).prod) = 989548687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_7
      · exact prime_seventyBP_7853561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 989548687) ^ 494774343 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 989548687) ^ 329849562 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 989548687) ^ 141364098 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 989548687) ^ 126 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1343551243 : Nat.Prime 1343551243 := by
  apply lucas_primality 1343551243 (2 : ZMod 1343551243)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (113, 1), (10597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (113, 1), (10597, 1)] : List FactorBlock).map factorBlockValue).prod) = 1343551243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_11
      · exact prime_seventyBP_17
      · exact prime_seventyBP_113
      · exact prime_seventyBP_10597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1343551243) ^ 671775621 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1343551243) ^ 447850414 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1343551243) ^ 122141022 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1343551243) ^ 79032426 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1343551243) ^ 11889834 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1343551243) ^ 126786 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1481796791 : Nat.Prime 1481796791 := by
  apply lucas_primality 1481796791 (26 : ZMod 1481796791)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 1), (67, 1), (41729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 1), (67, 1), (41729, 1)] : List FactorBlock).map factorBlockValue).prod) = 1481796791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_53
      · exact prime_seventyBP_67
      · exact prime_seventyBP_41729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 1481796791) ^ 740898395 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (26 : ZMod 1481796791) ^ 296359358 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (26 : ZMod 1481796791) ^ 27958430 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (26 : ZMod 1481796791) ^ 22116370 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (26 : ZMod 1481796791) ^ 35510 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1696574303 : Nat.Prime 1696574303 := by
  apply lucas_primality 1696574303 (5 : ZMod 1696574303)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1319, 1), (643129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1319, 1), (643129, 1)] : List FactorBlock).map factorBlockValue).prod) = 1696574303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_1319
      · exact prime_seventyBP_643129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1696574303) ^ 848287151 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1696574303) ^ 1286258 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1696574303) ^ 2638 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1716185509 : Nat.Prime 1716185509 := by
  apply lucas_primality 1716185509 (6 : ZMod 1716185509)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (143015459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (143015459, 1)] : List FactorBlock).map factorBlockValue).prod) = 1716185509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_143015459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1716185509) ^ 858092754 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1716185509) ^ 572061836 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1716185509) ^ 12 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1897959529 : Nat.Prime 1897959529 := by
  apply lucas_primality 1897959529 (13 : ZMod 1897959529)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (347, 1), (75967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (347, 1), (75967, 1)] : List FactorBlock).map factorBlockValue).prod) = 1897959529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_347
      · exact prime_seventyBP_75967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1897959529) ^ 948979764 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 1897959529) ^ 632653176 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 1897959529) ^ 5469624 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 1897959529) ^ 24984 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1971087073 : Nat.Prime 1971087073 := by
  apply lucas_primality 1971087073 (5 : ZMod 1971087073)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (20532157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (20532157, 1)] : List FactorBlock).map factorBlockValue).prod) = 1971087073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_20532157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1971087073) ^ 985543536 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1971087073) ^ 657029024 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1971087073) ^ 96 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_2001730781 : Nat.Prime 2001730781 := by
  apply lucas_primality 2001730781 (3 : ZMod 2001730781)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (14298077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (14298077, 1)] : List FactorBlock).map factorBlockValue).prod) = 2001730781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_7
      · exact prime_seventyBP_14298077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2001730781) ^ 1000865390 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2001730781) ^ 400346156 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2001730781) ^ 285961540 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2001730781) ^ 140 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_2072350739 : Nat.Prime 2072350739 := by
  apply lucas_primality 2072350739 (2 : ZMod 2072350739)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (173, 1), (260411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (173, 1), (260411, 1)] : List FactorBlock).map factorBlockValue).prod) = 2072350739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_23
      · exact prime_seventyBP_173
      · exact prime_seventyBP_260411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2072350739) ^ 1036175369 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072350739) ^ 90102206 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072350739) ^ 11978906 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072350739) ^ 7958 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_2106828827 : Nat.Prime 2106828827 := by
  apply lucas_primality 2106828827 (2 : ZMod 2106828827)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (367, 1), (32251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (367, 1), (32251, 1)] : List FactorBlock).map factorBlockValue).prod) = 2106828827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_89
      · exact prime_seventyBP_367
      · exact prime_seventyBP_32251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2106828827) ^ 1053414413 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2106828827) ^ 23672234 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2106828827) ^ 5740678 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2106828827) ^ 65326 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_2237949869 : Nat.Prime 2237949869 := by
  apply lucas_primality 2237949869 (2 : ZMod 2237949869)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (7266071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (7266071, 1)] : List FactorBlock).map factorBlockValue).prod) = 2237949869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_11
      · exact prime_seventyBP_7266071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2237949869) ^ 1118974934 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2237949869) ^ 319707124 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2237949869) ^ 203449988 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2237949869) ^ 308 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_2558157491 : Nat.Prime 2558157491 := by
  apply lucas_primality 2558157491 (6 : ZMod 2558157491)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (991, 1), (36877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (991, 1), (36877, 1)] : List FactorBlock).map factorBlockValue).prod) = 2558157491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_7
      · exact prime_seventyBP_991
      · exact prime_seventyBP_36877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2558157491) ^ 1279078745 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2558157491) ^ 511631498 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2558157491) ^ 365451070 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2558157491) ^ 2581390 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2558157491) ^ 69370 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_2874010981 : Nat.Prime 2874010981 := by
  apply lucas_primality 2874010981 (2 : ZMod 2874010981)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (47900183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (47900183, 1)] : List FactorBlock).map factorBlockValue).prod) = 2874010981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_47900183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2874010981) ^ 1437005490 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2874010981) ^ 958003660 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2874010981) ^ 574802196 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2874010981) ^ 60 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_3069150509 : Nat.Prime 3069150509 := by
  apply lucas_primality 3069150509 (2 : ZMod 3069150509)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2309, 1), (332303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2309, 1), (332303, 1)] : List FactorBlock).map factorBlockValue).prod) = 3069150509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_2309
      · exact prime_seventyBP_332303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3069150509) ^ 1534575254 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3069150509) ^ 1329212 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3069150509) ^ 9236 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_3283415249 : Nat.Prime 3283415249 := by
  apply lucas_primality 3283415249 (3 : ZMod 3283415249)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (205213453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (205213453, 1)] : List FactorBlock).map factorBlockValue).prod) = 3283415249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_205213453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 3283415249) ^ 1641707624 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3283415249) ^ 16 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_4164800047 : Nat.Prime 4164800047 := by
  apply lucas_primality 4164800047 (5 : ZMod 4164800047)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (3711943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (3711943, 1)] : List FactorBlock).map factorBlockValue).prod) = 4164800047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_11
      · exact prime_seventyBP_17
      · exact prime_seventyBP_3711943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4164800047) ^ 2082400023 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4164800047) ^ 1388266682 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4164800047) ^ 378618186 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4164800047) ^ 244988238 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4164800047) ^ 1122 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_4717261883 : Nat.Prime 4717261883 := by
  apply lucas_primality 4717261883 (2 : ZMod 4717261883)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (38666081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (38666081, 1)] : List FactorBlock).map factorBlockValue).prod) = 4717261883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_61
      · exact prime_seventyBP_38666081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4717261883) ^ 2358630941 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4717261883) ^ 77332162 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4717261883) ^ 122 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_4810033297 : Nat.Prime 4810033297 := by
  apply lucas_primality 4810033297 (15 : ZMod 4810033297)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (673, 1), (49633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (673, 1), (49633, 1)] : List FactorBlock).map factorBlockValue).prod) = 4810033297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_673
      · exact prime_seventyBP_49633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 4810033297) ^ 2405016648 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (15 : ZMod 4810033297) ^ 1603344432 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (15 : ZMod 4810033297) ^ 7147152 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (15 : ZMod 4810033297) ^ 96912 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_5349156443 : Nat.Prime 5349156443 := by
  apply lucas_primality 5349156443 (2 : ZMod 5349156443)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (54583229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (54583229, 1)] : List FactorBlock).map factorBlockValue).prod) = 5349156443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_54583229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5349156443) ^ 2674578221 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5349156443) ^ 764165206 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5349156443) ^ 98 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_5426567411 : Nat.Prime 5426567411 := by
  apply lucas_primality 5426567411 (2 : ZMod 5426567411)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (49332431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (49332431, 1)] : List FactorBlock).map factorBlockValue).prod) = 5426567411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_11
      · exact prime_seventyBP_49332431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5426567411) ^ 2713283705 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5426567411) ^ 1085313482 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5426567411) ^ 493324310 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5426567411) ^ 110 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_5589300061 : Nat.Prime 5589300061 := by
  apply lucas_primality 5589300061 (2 : ZMod 5589300061)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (179, 1), (173473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (179, 1), (173473, 1)] : List FactorBlock).map factorBlockValue).prod) = 5589300061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_179
      · exact prime_seventyBP_173473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5589300061) ^ 2794650030 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5589300061) ^ 1863100020 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5589300061) ^ 1117860012 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5589300061) ^ 31225140 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5589300061) ^ 32220 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_5793360847 : Nat.Prime 5793360847 := by
  apply lucas_primality 5793360847 (5 : ZMod 5793360847)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (13, 1), (43, 1), (35251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (13, 1), (43, 1), (35251, 1)] : List FactorBlock).map factorBlockValue).prod) = 5793360847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_7
      · exact prime_seventyBP_13
      · exact prime_seventyBP_43
      · exact prime_seventyBP_35251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5793360847) ^ 2896680423 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5793360847) ^ 1931120282 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5793360847) ^ 827622978 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5793360847) ^ 445643142 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5793360847) ^ 134729322 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5793360847) ^ 164346 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_6117259921 : Nat.Prime 6117259921 := by
  apply lucas_primality 6117259921 (21 : ZMod 6117259921)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (2437, 1), (10459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (2437, 1), (10459, 1)] : List FactorBlock).map factorBlockValue).prod) = 6117259921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_2437
      · exact prime_seventyBP_10459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 6117259921) ^ 3058629960 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (21 : ZMod 6117259921) ^ 2039086640 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (21 : ZMod 6117259921) ^ 1223451984 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (21 : ZMod 6117259921) ^ 2510160 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (21 : ZMod 6117259921) ^ 584880 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_6546142661 : Nat.Prime 6546142661 := by
  apply lucas_primality 6546142661 (3 : ZMod 6546142661)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (327307133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (327307133, 1)] : List FactorBlock).map factorBlockValue).prod) = 6546142661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_327307133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6546142661) ^ 3273071330 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6546142661) ^ 1309228532 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6546142661) ^ 20 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_6721328609 : Nat.Prime 6721328609 := by
  apply lucas_primality 6721328609 (3 : ZMod 6721328609)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (29, 1), (101, 1), (71711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (29, 1), (101, 1), (71711, 1)] : List FactorBlock).map factorBlockValue).prod) = 6721328609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_29
      · exact prime_seventyBP_101
      · exact prime_seventyBP_71711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6721328609) ^ 3360664304 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6721328609) ^ 231769952 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6721328609) ^ 66547808 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6721328609) ^ 93728 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_7725262513 : Nat.Prime 7725262513 := by
  apply lucas_primality 7725262513 (5 : ZMod 7725262513)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (109, 1), (269, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (109, 1), (269, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) = 7725262513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_11
      · exact prime_seventyBP_109
      · exact prime_seventyBP_269
      · exact prime_seventyBP_499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7725262513) ^ 3862631256 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 7725262513) ^ 2575087504 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 7725262513) ^ 702296592 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 7725262513) ^ 70873968 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 7725262513) ^ 28718448 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 7725262513) ^ 15481488 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_8070986711 : Nat.Prime 8070986711 := by
  apply lucas_primality 8070986711 (7 : ZMod 8070986711)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (26035441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (26035441, 1)] : List FactorBlock).map factorBlockValue).prod) = 8070986711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_31
      · exact prime_seventyBP_26035441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 8070986711) ^ 4035493355 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 8070986711) ^ 1614197342 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 8070986711) ^ 260354410 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 8070986711) ^ 310 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_8650384373 : Nat.Prime 8650384373 := by
  apply lucas_primality 8650384373 (2 : ZMod 8650384373)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (439, 1), (37039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (439, 1), (37039, 1)] : List FactorBlock).map factorBlockValue).prod) = 8650384373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_19
      · exact prime_seventyBP_439
      · exact prime_seventyBP_37039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8650384373) ^ 4325192186 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8650384373) ^ 1235769196 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8650384373) ^ 455283388 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8650384373) ^ 19704748 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8650384373) ^ 233548 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_9434523767 : Nat.Prime 9434523767 := by
  apply lucas_primality 9434523767 (5 : ZMod 9434523767)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4717261883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4717261883, 1)] : List FactorBlock).map factorBlockValue).prod) = 9434523767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_4717261883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 9434523767) ^ 4717261883 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 9434523767) ^ 2 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_9505082299 : Nat.Prime 9505082299 := by
  apply lucas_primality 9505082299 (3 : ZMod 9505082299)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (709, 1), (72077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (709, 1), (72077, 1)] : List FactorBlock).map factorBlockValue).prod) = 9505082299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_31
      · exact prime_seventyBP_709
      · exact prime_seventyBP_72077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9505082299) ^ 4752541149 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9505082299) ^ 3168360766 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9505082299) ^ 306615558 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9505082299) ^ 13406322 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9505082299) ^ 131874 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_9576383093 : Nat.Prime 9576383093 := by
  apply lucas_primality 9576383093 (2 : ZMod 9576383093)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (353, 1), (593, 1), (11437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (353, 1), (593, 1), (11437, 1)] : List FactorBlock).map factorBlockValue).prod) = 9576383093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_353
      · exact prime_seventyBP_593
      · exact prime_seventyBP_11437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9576383093) ^ 4788191546 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9576383093) ^ 27128564 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9576383093) ^ 16149044 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9576383093) ^ 837316 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_10107863849 : Nat.Prime 10107863849 := by
  apply lucas_primality 10107863849 (3 : ZMod 10107863849)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (211, 1), (457, 1), (13103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (211, 1), (457, 1), (13103, 1)] : List FactorBlock).map factorBlockValue).prod) = 10107863849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_211
      · exact prime_seventyBP_457
      · exact prime_seventyBP_13103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10107863849) ^ 5053931924 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 10107863849) ^ 47904568 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 10107863849) ^ 22117864 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 10107863849) ^ 771416 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_10383355777 : Nat.Prime 10383355777 := by
  apply lucas_primality 10383355777 (5 : ZMod 10383355777)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (83, 1), (325783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (83, 1), (325783, 1)] : List FactorBlock).map factorBlockValue).prod) = 10383355777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_83
      · exact prime_seventyBP_325783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10383355777) ^ 5191677888 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 10383355777) ^ 3461118592 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 10383355777) ^ 125100672 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 10383355777) ^ 31872 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_10747200017 : Nat.Prime 10747200017 := by
  apply lucas_primality 10747200017 (10 : ZMod 10747200017)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (29, 1), (3308867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (29, 1), (3308867, 1)] : List FactorBlock).map factorBlockValue).prod) = 10747200017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_29
      · exact prime_seventyBP_3308867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 10747200017) ^ 5373600008 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 10747200017) ^ 1535314288 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 10747200017) ^ 370593104 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 10747200017) ^ 3248 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_11197387057 : Nat.Prime 11197387057 := by
  apply lucas_primality 11197387057 (10 : ZMod 11197387057)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (233278897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (233278897, 1)] : List FactorBlock).map factorBlockValue).prod) = 11197387057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_233278897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 11197387057) ^ 5598693528 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 11197387057) ^ 3732462352 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 11197387057) ^ 48 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_11664396397 : Nat.Prime 11664396397 := by
  apply lucas_primality 11664396397 (2 : ZMod 11664396397)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (73, 1), (4438507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (73, 1), (4438507, 1)] : List FactorBlock).map factorBlockValue).prod) = 11664396397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_73
      · exact prime_seventyBP_4438507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11664396397) ^ 5832198198 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11664396397) ^ 3888132132 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11664396397) ^ 159786252 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11664396397) ^ 2628 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_12690274841 : Nat.Prime 12690274841 := by
  apply lucas_primality 12690274841 (3 : ZMod 12690274841)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (23, 1), (13793777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (23, 1), (13793777, 1)] : List FactorBlock).map factorBlockValue).prod) = 12690274841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_23
      · exact prime_seventyBP_13793777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12690274841) ^ 6345137420 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 12690274841) ^ 2538054968 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 12690274841) ^ 551751080 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 12690274841) ^ 920 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_15407818603 : Nat.Prime 15407818603 := by
  apply lucas_primality 15407818603 (3 : ZMod 15407818603)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (317, 1), (736441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (317, 1), (736441, 1)] : List FactorBlock).map factorBlockValue).prod) = 15407818603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_11
      · exact prime_seventyBP_317
      · exact prime_seventyBP_736441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15407818603) ^ 7703909301 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 15407818603) ^ 5135939534 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 15407818603) ^ 1400710782 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 15407818603) ^ 48605106 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 15407818603) ^ 20922 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_15888597061 : Nat.Prime 15888597061 := by
  apply lucas_primality 15888597061 (23 : ZMod 15888597061)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (367, 1), (103079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (367, 1), (103079, 1)] : List FactorBlock).map factorBlockValue).prod) = 15888597061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_7
      · exact prime_seventyBP_367
      · exact prime_seventyBP_103079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 15888597061) ^ 7944298530 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (23 : ZMod 15888597061) ^ 5296199020 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (23 : ZMod 15888597061) ^ 3177719412 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (23 : ZMod 15888597061) ^ 2269799580 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (23 : ZMod 15888597061) ^ 43293180 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (23 : ZMod 15888597061) ^ 154140 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_17409188107 : Nat.Prime 17409188107 := by
  apply lucas_primality 17409188107 (2 : ZMod 17409188107)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (2297, 1), (18307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (2297, 1), (18307, 1)] : List FactorBlock).map factorBlockValue).prod) = 17409188107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_23
      · exact prime_seventyBP_2297
      · exact prime_seventyBP_18307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17409188107) ^ 8704594053 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 17409188107) ^ 5803062702 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 17409188107) ^ 756921222 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 17409188107) ^ 7579098 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 17409188107) ^ 950958 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_20458774247 : Nat.Prime 20458774247 := by
  apply lucas_primality 20458774247 (5 : ZMod 20458774247)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (352737487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (352737487, 1)] : List FactorBlock).map factorBlockValue).prod) = 20458774247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_29
      · exact prime_seventyBP_352737487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 20458774247) ^ 10229387123 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 20458774247) ^ 705474974 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 20458774247) ^ 58 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_20594226109 : Nat.Prime 20594226109 := by
  apply lucas_primality 20594226109 (6 : ZMod 20594226109)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1716185509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1716185509, 1)] : List FactorBlock).map factorBlockValue).prod) = 20594226109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_1716185509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 20594226109) ^ 10297113054 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 20594226109) ^ 6864742036 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 20594226109) ^ 12 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_22971167231 : Nat.Prime 22971167231 := by
  apply lucas_primality 22971167231 (11 : ZMod 22971167231)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (208828793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (208828793, 1)] : List FactorBlock).map factorBlockValue).prod) = 22971167231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_11
      · exact prime_seventyBP_208828793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 22971167231) ^ 11485583615 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 22971167231) ^ 4594233446 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 22971167231) ^ 2088287930 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 22971167231) ^ 110 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_24553204073 : Nat.Prime 24553204073 := by
  apply lucas_primality 24553204073 (3 : ZMod 24553204073)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3069150509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3069150509, 1)] : List FactorBlock).map factorBlockValue).prod) = 24553204073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3069150509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 24553204073) ^ 12276602036 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 24553204073) ^ 8 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_25380549683 : Nat.Prime 25380549683 := by
  apply lucas_primality 25380549683 (2 : ZMod 25380549683)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12690274841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12690274841, 1)] : List FactorBlock).map factorBlockValue).prod) = 25380549683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_12690274841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 25380549683) ^ 12690274841 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 25380549683) ^ 2 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_32694419861 : Nat.Prime 32694419861 := by
  apply lucas_primality 32694419861 (2 : ZMod 32694419861)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 2), (4528313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 2), (4528313, 1)] : List FactorBlock).map factorBlockValue).prod) = 32694419861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_19
      · exact prime_seventyBP_4528313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32694419861) ^ 16347209930 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 32694419861) ^ 6538883972 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 32694419861) ^ 1720758940 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 32694419861) ^ 7220 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_46750164809 : Nat.Prime 46750164809 := by
  apply lucas_primality 46750164809 (3 : ZMod 46750164809)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2477, 1), (2359213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2477, 1), (2359213, 1)] : List FactorBlock).map factorBlockValue).prod) = 46750164809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_2477
      · exact prime_seventyBP_2359213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 46750164809) ^ 23375082404 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 46750164809) ^ 18873704 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 46750164809) ^ 19816 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_55178143847 : Nat.Prime 55178143847 := by
  apply lucas_primality 55178143847 (5 : ZMod 55178143847)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (461, 1), (449971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (461, 1), (449971, 1)] : List FactorBlock).map factorBlockValue).prod) = 55178143847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_19
      · exact prime_seventyBP_461
      · exact prime_seventyBP_449971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 55178143847) ^ 27589071923 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 55178143847) ^ 7882591978 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 55178143847) ^ 2904112834 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 55178143847) ^ 119692286 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 55178143847) ^ 122626 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_59553204941 : Nat.Prime 59553204941 := by
  apply lucas_primality 59553204941 (3 : ZMod 59553204941)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (129463489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (129463489, 1)] : List FactorBlock).map factorBlockValue).prod) = 59553204941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_23
      · exact prime_seventyBP_129463489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 59553204941) ^ 29776602470 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 59553204941) ^ 11910640988 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 59553204941) ^ 2589269780 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 59553204941) ^ 460 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_64186864999 : Nat.Prime 64186864999 := by
  apply lucas_primality 64186864999 (3 : ZMod 64186864999)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (135415327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (135415327, 1)] : List FactorBlock).map factorBlockValue).prod) = 64186864999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_79
      · exact prime_seventyBP_135415327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 64186864999) ^ 32093432499 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 64186864999) ^ 21395621666 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 64186864999) ^ 812491962 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 64186864999) ^ 474 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_70254208949 : Nat.Prime 70254208949 := by
  apply lucas_primality 70254208949 (2 : ZMod 70254208949)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (37, 1), (6164813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (37, 1), (6164813, 1)] : List FactorBlock).map factorBlockValue).prod) = 70254208949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_11
      · exact prime_seventyBP_37
      · exact prime_seventyBP_6164813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70254208949) ^ 35127104474 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 70254208949) ^ 10036315564 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 70254208949) ^ 6386746268 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 70254208949) ^ 1898762404 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 70254208949) ^ 11396 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_70507323541 : Nat.Prime 70507323541 := by
  apply lucas_primality 70507323541 (2 : ZMod 70507323541)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (17, 1), (47, 1), (490247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (17, 1), (47, 1), (490247, 1)] : List FactorBlock).map factorBlockValue).prod) = 70507323541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_17
      · exact prime_seventyBP_47
      · exact prime_seventyBP_490247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70507323541) ^ 35253661770 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 70507323541) ^ 23502441180 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 70507323541) ^ 14101464708 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 70507323541) ^ 4147489620 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 70507323541) ^ 1500155820 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 70507323541) ^ 143820 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_73745900077 : Nat.Prime 73745900077 := by
  apply lucas_primality 73745900077 (6 : ZMod 73745900077)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (2609, 1), (54779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (2609, 1), (54779, 1)] : List FactorBlock).map factorBlockValue).prod) = 73745900077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_43
      · exact prime_seventyBP_2609
      · exact prime_seventyBP_54779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 73745900077) ^ 36872950038 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 73745900077) ^ 24581966692 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 73745900077) ^ 1715020932 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 73745900077) ^ 28265964 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 73745900077) ^ 1346244 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_93689007337 : Nat.Prime 93689007337 := by
  apply lucas_primality 93689007337 (10 : ZMod 93689007337)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (3691, 1), (352543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (3691, 1), (352543, 1)] : List FactorBlock).map factorBlockValue).prod) = 93689007337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_3691
      · exact prime_seventyBP_352543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 93689007337) ^ 46844503668 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 93689007337) ^ 31229669112 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 93689007337) ^ 25383096 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 93689007337) ^ 265752 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_95575039969 : Nat.Prime 95575039969 := by
  apply lucas_primality 95575039969 (13 : ZMod 95575039969)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (30757, 1), (32369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (30757, 1), (32369, 1)] : List FactorBlock).map factorBlockValue).prod) = 95575039969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_30757
      · exact prime_seventyBP_32369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 95575039969) ^ 47787519984 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 95575039969) ^ 31858346656 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 95575039969) ^ 3107424 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 95575039969) ^ 2952672 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_121469409857 : Nat.Prime 121469409857 := by
  apply lucas_primality 121469409857 (3 : ZMod 121469409857)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (1897959529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (1897959529, 1)] : List FactorBlock).map factorBlockValue).prod) = 121469409857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_1897959529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 121469409857) ^ 60734704928 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 121469409857) ^ 64 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_136747622533 : Nat.Prime 136747622533 := by
  apply lucas_primality 136747622533 (5 : ZMod 136747622533)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (8293, 1), (80831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (8293, 1), (80831, 1)] : List FactorBlock).map factorBlockValue).prod) = 136747622533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_17
      · exact prime_seventyBP_8293
      · exact prime_seventyBP_80831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 136747622533) ^ 68373811266 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 136747622533) ^ 45582540844 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 136747622533) ^ 8043977796 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 136747622533) ^ 16489524 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 136747622533) ^ 1691772 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_148846574021 : Nat.Prime 148846574021 := by
  apply lucas_primality 148846574021 (2 : ZMod 148846574021)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (71, 1), (104821531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (71, 1), (104821531, 1)] : List FactorBlock).map factorBlockValue).prod) = 148846574021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_71
      · exact prime_seventyBP_104821531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 148846574021) ^ 74423287010 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 148846574021) ^ 29769314804 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 148846574021) ^ 2096430620 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 148846574021) ^ 1420 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_217879978931 : Nat.Prime 217879978931 := by
  apply lucas_primality 217879978931 (2 : ZMod 217879978931)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (863, 1), (25246811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (863, 1), (25246811, 1)] : List FactorBlock).map factorBlockValue).prod) = 217879978931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_863
      · exact prime_seventyBP_25246811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 217879978931) ^ 108939989465 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 217879978931) ^ 43575995786 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 217879978931) ^ 252468110 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 217879978931) ^ 8630 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_226428570409 : Nat.Prime 226428570409 := by
  apply lucas_primality 226428570409 (7 : ZMod 226428570409)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (9434523767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (9434523767, 1)] : List FactorBlock).map factorBlockValue).prod) = 226428570409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_9434523767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 226428570409) ^ 113214285204 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 226428570409) ^ 75476190136 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 226428570409) ^ 24 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_235040173961 : Nat.Prime 235040173961 := by
  apply lucas_primality 235040173961 (3 : ZMod 235040173961)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (331, 1), (17752279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (331, 1), (17752279, 1)] : List FactorBlock).map factorBlockValue).prod) = 235040173961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_331
      · exact prime_seventyBP_17752279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 235040173961) ^ 117520086980 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 235040173961) ^ 47008034792 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 235040173961) ^ 710091160 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 235040173961) ^ 13240 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_252180942061 : Nat.Prime 252180942061 := by
  apply lucas_primality 252180942061 (10 : ZMod 252180942061)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13553, 1), (310117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13553, 1), (310117, 1)] : List FactorBlock).map factorBlockValue).prod) = 252180942061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_13553
      · exact prime_seventyBP_310117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 252180942061) ^ 126090471030 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 252180942061) ^ 84060314020 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 252180942061) ^ 50436188412 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 252180942061) ^ 18607020 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 252180942061) ^ 813180 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_253566554179 : Nat.Prime 253566554179 := by
  apply lucas_primality 253566554179 (10 : ZMod 253566554179)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (71, 1), (2932151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (71, 1), (2932151, 1)] : List FactorBlock).map factorBlockValue).prod) = 253566554179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_7
      · exact prime_seventyBP_29
      · exact prime_seventyBP_71
      · exact prime_seventyBP_2932151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 253566554179) ^ 126783277089 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 253566554179) ^ 84522184726 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 253566554179) ^ 36223793454 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 253566554179) ^ 8743674282 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 253566554179) ^ 3571359918 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 253566554179) ^ 86478 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_308737237433 : Nat.Prime 308737237433 := by
  apply lucas_primality 308737237433 (3 : ZMod 308737237433)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (4861, 1), (610703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (4861, 1), (610703, 1)] : List FactorBlock).map factorBlockValue).prod) = 308737237433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_13
      · exact prime_seventyBP_4861
      · exact prime_seventyBP_610703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 308737237433) ^ 154368618716 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 308737237433) ^ 23749018264 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 308737237433) ^ 63513112 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 308737237433) ^ 505544 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_396206952469 : Nat.Prime 396206952469 := by
  apply lucas_primality 396206952469 (2 : ZMod 396206952469)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (492794717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (492794717, 1)] : List FactorBlock).map factorBlockValue).prod) = 396206952469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_67
      · exact prime_seventyBP_492794717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 396206952469) ^ 198103476234 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 396206952469) ^ 132068984156 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 396206952469) ^ 5913536604 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 396206952469) ^ 804 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_431868861751 : Nat.Prime 431868861751 := by
  apply lucas_primality 431868861751 (13 : ZMod 431868861751)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (2689, 1), (214141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (2689, 1), (214141, 1)] : List FactorBlock).map factorBlockValue).prod) = 431868861751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_2689
      · exact prime_seventyBP_214141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 431868861751) ^ 215934430875 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 431868861751) ^ 143956287250 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 431868861751) ^ 86373772350 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 431868861751) ^ 160605750 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 431868861751) ^ 2016750 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_552015942727 : Nat.Prime 552015942727 := by
  apply lucas_primality 552015942727 (3 : ZMod 552015942727)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (47, 1), (5821, 1), (14621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (47, 1), (5821, 1), (14621, 1)] : List FactorBlock).map factorBlockValue).prod) = 552015942727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_23
      · exact prime_seventyBP_47
      · exact prime_seventyBP_5821
      · exact prime_seventyBP_14621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 552015942727) ^ 276007971363 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 552015942727) ^ 184005314242 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 552015942727) ^ 24000693162 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 552015942727) ^ 11745020058 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 552015942727) ^ 94831806 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 552015942727) ^ 37755006 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_582579355067 : Nat.Prime 582579355067 := by
  apply lucas_primality 582579355067 (2 : ZMod 582579355067)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6323, 1), (46068271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6323, 1), (46068271, 1)] : List FactorBlock).map factorBlockValue).prod) = 582579355067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_6323
      · exact prime_seventyBP_46068271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 582579355067) ^ 291289677533 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 582579355067) ^ 92136542 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 582579355067) ^ 12646 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_616312744121 : Nat.Prime 616312744121 := by
  apply lucas_primality 616312744121 (3 : ZMod 616312744121)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (15407818603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (15407818603, 1)] : List FactorBlock).map factorBlockValue).prod) = 616312744121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_15407818603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 616312744121) ^ 308156372060 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 616312744121) ^ 123262548824 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 616312744121) ^ 40 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_727060585421 : Nat.Prime 727060585421 := by
  apply lucas_primality 727060585421 (2 : ZMod 727060585421)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (179, 1), (15622273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (179, 1), (15622273, 1)] : List FactorBlock).map factorBlockValue).prod) = 727060585421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_13
      · exact prime_seventyBP_179
      · exact prime_seventyBP_15622273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 727060585421) ^ 363530292710 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 727060585421) ^ 145412117084 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 727060585421) ^ 55927737340 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 727060585421) ^ 4061790980 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 727060585421) ^ 46540 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_730891876193 : Nat.Prime 730891876193 := by
  apply lucas_primality 730891876193 (3 : ZMod 730891876193)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17, 1), (1343551243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17, 1), (1343551243, 1)] : List FactorBlock).map factorBlockValue).prod) = 730891876193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_17
      · exact prime_seventyBP_1343551243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 730891876193) ^ 365445938096 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 730891876193) ^ 42993639776 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 730891876193) ^ 544 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_909356595311 : Nat.Prime 909356595311 := by
  apply lucas_primality 909356595311 (13 : ZMod 909356595311)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (5349156443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (5349156443, 1)] : List FactorBlock).map factorBlockValue).prod) = 909356595311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_17
      · exact prime_seventyBP_5349156443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 909356595311) ^ 454678297655 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 909356595311) ^ 181871319062 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 909356595311) ^ 53491564430 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 909356595311) ^ 170 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_977908688083 : Nat.Prime 977908688083 := by
  apply lucas_primality 977908688083 (3 : ZMod 977908688083)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5881, 1), (9237929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5881, 1), (9237929, 1)] : List FactorBlock).map factorBlockValue).prod) = 977908688083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5881
      · exact prime_seventyBP_9237929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 977908688083) ^ 488954344041 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 977908688083) ^ 325969562694 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 977908688083) ^ 166282722 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 977908688083) ^ 105858 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_988522853233 : Nat.Prime 988522853233 := by
  apply lucas_primality 988522853233 (10 : ZMod 988522853233)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (20594226109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (20594226109, 1)] : List FactorBlock).map factorBlockValue).prod) = 988522853233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_20594226109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 988522853233) ^ 494261426616 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 988522853233) ^ 329507617744 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 988522853233) ^ 48 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_990162004453 : Nat.Prime 990162004453 := by
  apply lucas_primality 990162004453 (6 : ZMod 990162004453)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (97, 1), (929, 1), (48193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (97, 1), (929, 1), (48193, 1)] : List FactorBlock).map factorBlockValue).prod) = 990162004453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_19
      · exact prime_seventyBP_97
      · exact prime_seventyBP_929
      · exact prime_seventyBP_48193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 990162004453) ^ 495081002226 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 990162004453) ^ 330054001484 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 990162004453) ^ 52113789708 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 990162004453) ^ 10207855716 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 990162004453) ^ 1065836388 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 990162004453) ^ 20545764 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1011526896161 : Nat.Prime 1011526896161 := by
  apply lucas_primality 1011526896161 (3 : ZMod 1011526896161)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (11, 1), (131, 1), (2053, 1), (2137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (11, 1), (131, 1), (2053, 1), (2137, 1)] : List FactorBlock).map factorBlockValue).prod) = 1011526896161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_11
      · exact prime_seventyBP_131
      · exact prime_seventyBP_2053
      · exact prime_seventyBP_2137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1011526896161) ^ 505763448080 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1011526896161) ^ 202305379232 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1011526896161) ^ 91956990560 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1011526896161) ^ 7721579360 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1011526896161) ^ 492706720 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1011526896161) ^ 473339680 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1052622037609 : Nat.Prime 1052622037609 := by
  apply lucas_primality 1052622037609 (11 : ZMod 1052622037609)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (181, 1), (2753, 1), (88019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (181, 1), (2753, 1), (88019, 1)] : List FactorBlock).map factorBlockValue).prod) = 1052622037609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_181
      · exact prime_seventyBP_2753
      · exact prime_seventyBP_88019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1052622037609) ^ 526311018804 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 1052622037609) ^ 350874012536 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 1052622037609) ^ 5815591368 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 1052622037609) ^ 382354536 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 1052622037609) ^ 11959032 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1259096103887 : Nat.Prime 1259096103887 := by
  apply lucas_primality 1259096103887 (10 : ZMod 1259096103887)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (53, 1), (13457, 1), (46457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (53, 1), (13457, 1), (46457, 1)] : List FactorBlock).map factorBlockValue).prod) = 1259096103887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_19
      · exact prime_seventyBP_53
      · exact prime_seventyBP_13457
      · exact prime_seventyBP_46457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1259096103887) ^ 629548051943 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 1259096103887) ^ 66268215994 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 1259096103887) ^ 23756530262 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 1259096103887) ^ 93564398 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 1259096103887) ^ 27102398 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1344970227301 : Nat.Prime 1344970227301 := by
  apply lucas_primality 1344970227301 (2 : ZMod 1344970227301)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (7, 1), (19, 2), (29, 1), (131, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (7, 1), (19, 2), (29, 1), (131, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) = 1344970227301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_7
      · exact prime_seventyBP_19
      · exact prime_seventyBP_29
      · exact prime_seventyBP_131
      · exact prime_seventyBP_467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1344970227301) ^ 672485113650 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1344970227301) ^ 448323409100 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1344970227301) ^ 268994045460 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1344970227301) ^ 192138603900 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1344970227301) ^ 70787906700 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1344970227301) ^ 46378283700 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1344970227301) ^ 10266948300 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1344970227301) ^ 2880021900 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1398753491981 : Nat.Prime 1398753491981 := by
  apply lucas_primality 1398753491981 (3 : ZMod 1398753491981)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (199, 1), (593, 1), (45589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (199, 1), (593, 1), (45589, 1)] : List FactorBlock).map factorBlockValue).prod) = 1398753491981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_13
      · exact prime_seventyBP_199
      · exact prime_seventyBP_593
      · exact prime_seventyBP_45589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1398753491981) ^ 699376745990 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1398753491981) ^ 279750698396 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1398753491981) ^ 107596422460 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1398753491981) ^ 7028912020 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1398753491981) ^ 2358774860 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1398753491981) ^ 30681820 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_2312301072071 : Nat.Prime 2312301072071 := by
  apply lucas_primality 2312301072071 (7 : ZMod 2312301072071)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (1033, 1), (20349389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (1033, 1), (20349389, 1)] : List FactorBlock).map factorBlockValue).prod) = 2312301072071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_11
      · exact prime_seventyBP_1033
      · exact prime_seventyBP_20349389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2312301072071) ^ 1156150536035 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2312301072071) ^ 462460214414 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2312301072071) ^ 210209188370 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2312301072071) ^ 2238432790 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2312301072071) ^ 113630 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_2411041787669 : Nat.Prime 2411041787669 := by
  apply lucas_primality 2411041787669 (2 : ZMod 2411041787669)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101, 1), (9029, 1), (660973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101, 1), (9029, 1), (660973, 1)] : List FactorBlock).map factorBlockValue).prod) = 2411041787669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_101
      · exact prime_seventyBP_9029
      · exact prime_seventyBP_660973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2411041787669) ^ 1205520893834 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2411041787669) ^ 23871700868 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2411041787669) ^ 267033092 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2411041787669) ^ 3647716 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_2709664143337 : Nat.Prime 2709664143337 := by
  apply lucas_primality 2709664143337 (5 : ZMod 2709664143337)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (59, 1), (67, 1), (499, 1), (19079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (59, 1), (67, 1), (499, 1), (19079, 1)] : List FactorBlock).map factorBlockValue).prod) = 2709664143337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_59
      · exact prime_seventyBP_67
      · exact prime_seventyBP_499
      · exact prime_seventyBP_19079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2709664143337) ^ 1354832071668 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709664143337) ^ 903221381112 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709664143337) ^ 45926510904 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709664143337) ^ 40442748408 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709664143337) ^ 5430188664 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709664143337) ^ 142023384 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_2864228394581 : Nat.Prime 2864228394581 := by
  apply lucas_primality 2864228394581 (2 : ZMod 2864228394581)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (20458774247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (20458774247, 1)] : List FactorBlock).map factorBlockValue).prod) = 2864228394581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_7
      · exact prime_seventyBP_20458774247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2864228394581) ^ 1432114197290 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2864228394581) ^ 572845678916 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2864228394581) ^ 409175484940 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2864228394581) ^ 140 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_3359388237217 : Nat.Prime 3359388237217 := by
  apply lucas_primality 3359388237217 (5 : ZMod 3359388237217)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (7703, 1), (412987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (7703, 1), (412987, 1)] : List FactorBlock).map factorBlockValue).prod) = 3359388237217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_11
      · exact prime_seventyBP_7703
      · exact prime_seventyBP_412987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3359388237217) ^ 1679694118608 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3359388237217) ^ 1119796079072 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3359388237217) ^ 305398930656 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3359388237217) ^ 436114272 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3359388237217) ^ 8134368 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_4312989232631 : Nat.Prime 4312989232631 := by
  apply lucas_primality 4312989232631 (7 : ZMod 4312989232631)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (4759, 1), (6971389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (4759, 1), (6971389, 1)] : List FactorBlock).map factorBlockValue).prod) = 4312989232631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_13
      · exact prime_seventyBP_4759
      · exact prime_seventyBP_6971389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4312989232631) ^ 2156494616315 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 4312989232631) ^ 862597846526 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 4312989232631) ^ 331768402510 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 4312989232631) ^ 906280570 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 4312989232631) ^ 618670 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_4512232619339 : Nat.Prime 4512232619339 := by
  apply lucas_primality 4512232619339 (2 : ZMod 4512232619339)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3407, 1), (662200267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3407, 1), (662200267, 1)] : List FactorBlock).map factorBlockValue).prod) = 4512232619339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3407
      · exact prime_seventyBP_662200267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4512232619339) ^ 2256116309669 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4512232619339) ^ 1324400534 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4512232619339) ^ 6814 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_5011408325089 : Nat.Prime 5011408325089 := by
  apply lucas_primality 5011408325089 (14 : ZMod 5011408325089)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (11, 3), (4357807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (11, 3), (4357807, 1)] : List FactorBlock).map factorBlockValue).prod) = 5011408325089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_11
      · exact prime_seventyBP_4357807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 5011408325089) ^ 2505704162544 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (14 : ZMod 5011408325089) ^ 1670469441696 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (14 : ZMod 5011408325089) ^ 455582575008 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (14 : ZMod 5011408325089) ^ 1149984 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_6120887545769 : Nat.Prime 6120887545769 := by
  apply lucas_primality 6120887545769 (3 : ZMod 6120887545769)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (163, 1), (769, 1), (6103943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (163, 1), (769, 1), (6103943, 1)] : List FactorBlock).map factorBlockValue).prod) = 6120887545769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_163
      · exact prime_seventyBP_769
      · exact prime_seventyBP_6103943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6120887545769) ^ 3060443772884 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6120887545769) ^ 37551457336 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6120887545769) ^ 7959541672 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6120887545769) ^ 1002776 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_6637131006931 : Nat.Prime 6637131006931 := by
  apply lucas_primality 6637131006931 (2 : ZMod 6637131006931)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (73745900077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (73745900077, 1)] : List FactorBlock).map factorBlockValue).prod) = 6637131006931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_73745900077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6637131006931) ^ 3318565503465 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6637131006931) ^ 2212377002310 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6637131006931) ^ 1327426201386 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6637131006931) ^ 90 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_13301099508407 : Nat.Prime 13301099508407 := by
  apply lucas_primality 13301099508407 (5 : ZMod 13301099508407)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (269, 1), (53093, 1), (465659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (269, 1), (53093, 1), (465659, 1)] : List FactorBlock).map factorBlockValue).prod) = 13301099508407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_269
      · exact prime_seventyBP_53093
      · exact prime_seventyBP_465659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 13301099508407) ^ 6650549754203 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 13301099508407) ^ 49446466574 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 13301099508407) ^ 250524542 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 13301099508407) ^ 28564034 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_13808023341029 : Nat.Prime 13808023341029 := by
  apply lucas_primality 13808023341029 (2 : ZMod 13808023341029)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2903, 1), (169873817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2903, 1), (169873817, 1)] : List FactorBlock).map factorBlockValue).prod) = 13808023341029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_2903
      · exact prime_seventyBP_169873817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13808023341029) ^ 6904011670514 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13808023341029) ^ 1972574763004 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13808023341029) ^ 4756466876 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13808023341029) ^ 81284 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_13931608828453 : Nat.Prime 13931608828453 := by
  apply lucas_primality 13931608828453 (5 : ZMod 13931608828453)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (47, 1), (167, 1), (21130397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (47, 1), (167, 1), (21130397, 1)] : List FactorBlock).map factorBlockValue).prod) = 13931608828453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_7
      · exact prime_seventyBP_47
      · exact prime_seventyBP_167
      · exact prime_seventyBP_21130397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 13931608828453) ^ 6965804414226 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 13931608828453) ^ 4643869609484 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 13931608828453) ^ 1990229832636 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 13931608828453) ^ 296417209116 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 13931608828453) ^ 83422807356 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 13931608828453) ^ 659316 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_15599066864357 : Nat.Prime 15599066864357 := by
  apply lucas_primality 15599066864357 (2 : ZMod 15599066864357)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (103171, 1), (37799059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (103171, 1), (37799059, 1)] : List FactorBlock).map factorBlockValue).prod) = 15599066864357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_103171
      · exact prime_seventyBP_37799059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15599066864357) ^ 7799533432178 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 15599066864357) ^ 151196236 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 15599066864357) ^ 412684 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_15599571035801 : Nat.Prime 15599571035801 := by
  apply lucas_primality 15599571035801 (3 : ZMod 15599571035801)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (199, 1), (547, 1), (716543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (199, 1), (547, 1), (716543, 1)] : List FactorBlock).map factorBlockValue).prod) = 15599571035801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_199
      · exact prime_seventyBP_547
      · exact prime_seventyBP_716543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15599571035801) ^ 7799785517900 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 15599571035801) ^ 3119914207160 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 15599571035801) ^ 78389804200 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 15599571035801) ^ 28518411400 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 15599571035801) ^ 21770600 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_20156329423303 : Nat.Prime 20156329423303 := by
  apply lucas_primality 20156329423303 (5 : ZMod 20156329423303)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3359388237217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3359388237217, 1)] : List FactorBlock).map factorBlockValue).prod) = 20156329423303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_3359388237217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 20156329423303) ^ 10078164711651 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 20156329423303) ^ 6718776474434 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 20156329423303) ^ 6 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_20848970976403 : Nat.Prime 20848970976403 := by
  apply lucas_primality 20848970976403 (2 : ZMod 20848970976403)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (6689, 1), (22586261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (6689, 1), (22586261, 1)] : List FactorBlock).map factorBlockValue).prod) = 20848970976403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_23
      · exact prime_seventyBP_6689
      · exact prime_seventyBP_22586261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20848970976403) ^ 10424485488201 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20848970976403) ^ 6949656992134 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20848970976403) ^ 906476998974 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20848970976403) ^ 3116904018 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20848970976403) ^ 923082 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_20915141027449 : Nat.Prime 20915141027449 := by
  apply lucas_primality 20915141027449 (13 : ZMod 20915141027449)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (5503, 1), (3369397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (5503, 1), (3369397, 1)] : List FactorBlock).map factorBlockValue).prod) = 20915141027449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_47
      · exact prime_seventyBP_5503
      · exact prime_seventyBP_3369397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 20915141027449) ^ 10457570513724 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 20915141027449) ^ 6971713675816 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 20915141027449) ^ 445003000584 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 20915141027449) ^ 3800679816 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 20915141027449) ^ 6207384 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_23700774578801 : Nat.Prime 23700774578801 := by
  apply lucas_primality 23700774578801 (6 : ZMod 23700774578801)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (11, 1), (149, 1), (197, 1), (183509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (11, 1), (149, 1), (197, 1), (183509, 1)] : List FactorBlock).map factorBlockValue).prod) = 23700774578801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_11
      · exact prime_seventyBP_149
      · exact prime_seventyBP_197
      · exact prime_seventyBP_183509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 23700774578801) ^ 11850387289400 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 23700774578801) ^ 4740154915760 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 23700774578801) ^ 2154615870800 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 23700774578801) ^ 159065601200 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 23700774578801) ^ 120308500400 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 23700774578801) ^ 129153200 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_34370740734973 : Nat.Prime 34370740734973 := by
  apply lucas_primality 34370740734973 (5 : ZMod 34370740734973)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2864228394581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2864228394581, 1)] : List FactorBlock).map factorBlockValue).prod) = 34370740734973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_2864228394581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 34370740734973) ^ 17185370367486 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 34370740734973) ^ 11456913578324 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 34370740734973) ^ 12 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_38320833528721 : Nat.Prime 38320833528721 := by
  apply lucas_primality 38320833528721 (22 : ZMod 38320833528721)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (17, 1), (109, 1), (28722817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (17, 1), (109, 1), (28722817, 1)] : List FactorBlock).map factorBlockValue).prod) = 38320833528721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_17
      · exact prime_seventyBP_109
      · exact prime_seventyBP_28722817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 38320833528721) ^ 19160416764360 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (22 : ZMod 38320833528721) ^ 12773611176240 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (22 : ZMod 38320833528721) ^ 7664166705744 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (22 : ZMod 38320833528721) ^ 2254166678160 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (22 : ZMod 38320833528721) ^ 351567280080 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (22 : ZMod 38320833528721) ^ 1334160 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_41091581196691 : Nat.Prime 41091581196691 := by
  apply lucas_primality 41091581196691 (3 : ZMod 41091581196691)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (59, 1), (733, 1), (31672009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (59, 1), (733, 1), (31672009, 1)] : List FactorBlock).map factorBlockValue).prod) = 41091581196691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_59
      · exact prime_seventyBP_733
      · exact prime_seventyBP_31672009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 41091581196691) ^ 20545790598345 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 41091581196691) ^ 13697193732230 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 41091581196691) ^ 8218316239338 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 41091581196691) ^ 696467477910 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 41091581196691) ^ 56059455930 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 41091581196691) ^ 1297410 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_42160053301651 : Nat.Prime 42160053301651 := by
  apply lucas_primality 42160053301651 (2 : ZMod 42160053301651)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (93689007337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (93689007337, 1)] : List FactorBlock).map factorBlockValue).prod) = 42160053301651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_93689007337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 42160053301651) ^ 21080026650825 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 42160053301651) ^ 14053351100550 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 42160053301651) ^ 8432010660330 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 42160053301651) ^ 450 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_46661254768651 : Nat.Prime 46661254768651 := by
  apply lucas_primality 46661254768651 (3 : ZMod 46661254768651)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (139, 1), (2237949869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (139, 1), (2237949869, 1)] : List FactorBlock).map factorBlockValue).prod) = 46661254768651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_139
      · exact prime_seventyBP_2237949869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46661254768651) ^ 23330627384325 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 46661254768651) ^ 15553751589550 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 46661254768651) ^ 9332250953730 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 46661254768651) ^ 335692480350 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 46661254768651) ^ 20850 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_56986067069707 : Nat.Prime 56986067069707 := by
  apply lucas_primality 56986067069707 (2 : ZMod 56986067069707)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (733, 1), (5279, 1), (2454493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (733, 1), (5279, 1), (2454493, 1)] : List FactorBlock).map factorBlockValue).prod) = 56986067069707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_733
      · exact prime_seventyBP_5279
      · exact prime_seventyBP_2454493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56986067069707) ^ 28493033534853 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 56986067069707) ^ 18995355689902 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 56986067069707) ^ 77743611282 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 56986067069707) ^ 10794860214 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 56986067069707) ^ 23217042 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_62586156037313 : Nat.Prime 62586156037313 := by
  apply lucas_primality 62586156037313 (3 : ZMod 62586156037313)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (977908688083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (977908688083, 1)] : List FactorBlock).map factorBlockValue).prod) = 62586156037313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_977908688083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 62586156037313) ^ 31293078018656 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 62586156037313) ^ 64 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_69311340311711 : Nat.Prime 69311340311711 := by
  apply lucas_primality 69311340311711 (11 : ZMod 69311340311711)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (990162004453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (990162004453, 1)] : List FactorBlock).map factorBlockValue).prod) = 69311340311711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_7
      · exact prime_seventyBP_990162004453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 69311340311711) ^ 34655670155855 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 69311340311711) ^ 13862268062342 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 69311340311711) ^ 9901620044530 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 69311340311711) ^ 70 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_79710357275233 : Nat.Prime 79710357275233 := by
  apply lucas_primality 79710357275233 (7 : ZMod 79710357275233)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (83, 1), (5927, 1), (1687837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (83, 1), (5927, 1), (1687837, 1)] : List FactorBlock).map factorBlockValue).prod) = 79710357275233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_83
      · exact prime_seventyBP_5927
      · exact prime_seventyBP_1687837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 79710357275233) ^ 39855178637616 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 79710357275233) ^ 26570119091744 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 79710357275233) ^ 960365750304 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 79710357275233) ^ 13448685216 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 79710357275233) ^ 47226336 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_83395883905613 : Nat.Prime 83395883905613 := by
  apply lucas_primality 83395883905613 (2 : ZMod 83395883905613)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (20848970976403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (20848970976403, 1)] : List FactorBlock).map factorBlockValue).prod) = 83395883905613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_20848970976403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 83395883905613) ^ 41697941952806 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 83395883905613) ^ 4 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_102362865264953 : Nat.Prime 102362865264953 := by
  apply lucas_primality 102362865264953 (3 : ZMod 102362865264953)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (55667, 1), (229855357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (55667, 1), (229855357, 1)] : List FactorBlock).map factorBlockValue).prod) = 102362865264953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_55667
      · exact prime_seventyBP_229855357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 102362865264953) ^ 51181432632476 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 102362865264953) ^ 1838842856 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 102362865264953) ^ 445336 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_142703439437089 : Nat.Prime 142703439437089 := by
  apply lucas_primality 142703439437089 (7 : ZMod 142703439437089)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 6), (6117259921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 6), (6117259921, 1)] : List FactorBlock).map factorBlockValue).prod) = 142703439437089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_6117259921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 142703439437089) ^ 71351719718544 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 142703439437089) ^ 47567813145696 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 142703439437089) ^ 23328 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_171987402485603 : Nat.Prime 171987402485603 := by
  apply lucas_primality 171987402485603 (2 : ZMod 171987402485603)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (31, 1), (252180942061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (31, 1), (252180942061, 1)] : List FactorBlock).map factorBlockValue).prod) = 171987402485603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_11
      · exact prime_seventyBP_31
      · exact prime_seventyBP_252180942061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 171987402485603) ^ 85993701242801 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 171987402485603) ^ 15635218407782 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 171987402485603) ^ 5547980725342 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 171987402485603) ^ 682 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_197414213798507 : Nat.Prime 197414213798507 := by
  apply lucas_primality 197414213798507 (2 : ZMod 197414213798507)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (813997, 1), (1707919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (813997, 1), (1707919, 1)] : List FactorBlock).map factorBlockValue).prod) = 197414213798507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_71
      · exact prime_seventyBP_813997
      · exact prime_seventyBP_1707919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 197414213798507) ^ 98707106899253 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 197414213798507) ^ 2780481884486 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 197414213798507) ^ 242524498 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 197414213798507) ^ 115587574 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_230629330759027 : Nat.Prime 230629330759027 := by
  apply lucas_primality 230629330759027 (3 : ZMod 230629330759027)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1656101, 1), (23210071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1656101, 1), (23210071, 1)] : List FactorBlock).map factorBlockValue).prod) = 230629330759027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_1656101
      · exact prime_seventyBP_23210071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 230629330759027) ^ 115314665379513 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 230629330759027) ^ 76876443586342 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 230629330759027) ^ 139260426 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 230629330759027) ^ 9936606 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_318841429100933 : Nat.Prime 318841429100933 := by
  apply lucas_primality 318841429100933 (2 : ZMod 318841429100933)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79710357275233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79710357275233, 1)] : List FactorBlock).map factorBlockValue).prod) = 318841429100933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_79710357275233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 318841429100933) ^ 159420714550466 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 318841429100933) ^ 4 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_592951937457647 : Nat.Prime 592951937457647 := by
  apply lucas_primality 592951937457647 (5 : ZMod 592951937457647)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (167, 1), (659, 1), (1741, 1), (119027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (167, 1), (659, 1), (1741, 1), (119027, 1)] : List FactorBlock).map factorBlockValue).prod) = 592951937457647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_13
      · exact prime_seventyBP_167
      · exact prime_seventyBP_659
      · exact prime_seventyBP_1741
      · exact prime_seventyBP_119027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 592951937457647) ^ 296475968728823 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 592951937457647) ^ 45611687496742 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 592951937457647) ^ 3550610403938 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 592951937457647) ^ 899775322394 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 592951937457647) ^ 340581239206 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 592951937457647) ^ 4981659098 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_638342838067157 : Nat.Prime 638342838067157 := by
  apply lucas_primality 638342838067157 (2 : ZMod 638342838067157)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8663621, 1), (18420209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8663621, 1), (18420209, 1)] : List FactorBlock).map factorBlockValue).prod) = 638342838067157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_8663621
      · exact prime_seventyBP_18420209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 638342838067157) ^ 319171419033578 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 638342838067157) ^ 73680836 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 638342838067157) ^ 34654484 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_671204764798873 : Nat.Prime 671204764798873 := by
  apply lucas_primality 671204764798873 (5 : ZMod 671204764798873)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (227, 1), (1423, 1), (86579093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (227, 1), (1423, 1), (86579093, 1)] : List FactorBlock).map factorBlockValue).prod) = 671204764798873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_227
      · exact prime_seventyBP_1423
      · exact prime_seventyBP_86579093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 671204764798873) ^ 335602382399436 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 671204764798873) ^ 223734921599624 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 671204764798873) ^ 2956849184136 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 671204764798873) ^ 471682898664 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 671204764798873) ^ 7752504 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_717391304901409 : Nat.Prime 717391304901409 := by
  apply lucas_primality 717391304901409 (7 : ZMod 717391304901409)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (15461, 1), (483333943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (15461, 1), (483333943, 1)] : List FactorBlock).map factorBlockValue).prod) = 717391304901409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_15461
      · exact prime_seventyBP_483333943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 717391304901409) ^ 358695652450704 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 717391304901409) ^ 239130434967136 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 717391304901409) ^ 46400058528 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 717391304901409) ^ 1484256 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_747507264070253 : Nat.Prime 747507264070253 := by
  apply lucas_primality 747507264070253 (2 : ZMod 747507264070253)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (1327, 1), (2874010981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (1327, 1), (2874010981, 1)] : List FactorBlock).map factorBlockValue).prod) = 747507264070253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_1327
      · exact prime_seventyBP_2874010981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 747507264070253) ^ 373753632035126 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 747507264070253) ^ 106786752010036 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 747507264070253) ^ 563306152276 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 747507264070253) ^ 260092 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_767931652848037 : Nat.Prime 767931652848037 := by
  apply lucas_primality 767931652848037 (5 : ZMod 767931652848037)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (997, 1), (64186864999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (997, 1), (64186864999, 1)] : List FactorBlock).map factorBlockValue).prod) = 767931652848037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_997
      · exact prime_seventyBP_64186864999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 767931652848037) ^ 383965826424018 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 767931652848037) ^ 255977217616012 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 767931652848037) ^ 770242379988 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 767931652848037) ^ 11964 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1090212237000071 : Nat.Prime 1090212237000071 := by
  apply lucas_primality 1090212237000071 (19 : ZMod 1090212237000071)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (89, 1), (631, 1), (45146411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (89, 1), (631, 1), (45146411, 1)] : List FactorBlock).map factorBlockValue).prod) = 1090212237000071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_43
      · exact prime_seventyBP_89
      · exact prime_seventyBP_631
      · exact prime_seventyBP_45146411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1090212237000071) ^ 545106118500035 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (19 : ZMod 1090212237000071) ^ 218042447400014 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (19 : ZMod 1090212237000071) ^ 25353772953490 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (19 : ZMod 1090212237000071) ^ 12249575696630 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (19 : ZMod 1090212237000071) ^ 1727753148970 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (19 : ZMod 1090212237000071) ^ 24148370 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1407804135526871 : Nat.Prime 1407804135526871 := by
  apply lucas_primality 1407804135526871 (11 : ZMod 1407804135526871)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (6120887545769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (6120887545769, 1)] : List FactorBlock).map factorBlockValue).prod) = 1407804135526871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_23
      · exact prime_seventyBP_6120887545769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1407804135526871) ^ 703902067763435 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 1407804135526871) ^ 281560827105374 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 1407804135526871) ^ 61208875457690 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 1407804135526871) ^ 230 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1553045633639659 : Nat.Prime 1553045633639659 := by
  apply lucas_primality 1553045633639659 (2 : ZMod 1553045633639659)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (719, 1), (332309, 1), (361111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (719, 1), (332309, 1), (361111, 1)] : List FactorBlock).map factorBlockValue).prod) = 1553045633639659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_719
      · exact prime_seventyBP_332309
      · exact prime_seventyBP_361111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1553045633639659) ^ 776522816819829 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1553045633639659) ^ 517681877879886 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1553045633639659) ^ 2160007835382 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1553045633639659) ^ 4673498562 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1553045633639659) ^ 4300743078 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_2306198038899011 : Nat.Prime 2306198038899011 := by
  apply lucas_primality 2306198038899011 (2 : ZMod 2306198038899011)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (47, 1), (137, 1), (2106828827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (47, 1), (137, 1), (2106828827, 1)] : List FactorBlock).map factorBlockValue).prod) = 2306198038899011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_17
      · exact prime_seventyBP_47
      · exact prime_seventyBP_137
      · exact prime_seventyBP_2106828827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2306198038899011) ^ 1153099019449505 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2306198038899011) ^ 461239607779802 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2306198038899011) ^ 135658708170530 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2306198038899011) ^ 49068043380830 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2306198038899011) ^ 16833562327730 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2306198038899011) ^ 1094630 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_2894771603660389 : Nat.Prime 2894771603660389 := by
  apply lucas_primality 2894771603660389 (2 : ZMod 2894771603660389)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (23, 1), (552015942727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (23, 1), (552015942727, 1)] : List FactorBlock).map factorBlockValue).prod) = 2894771603660389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_19
      · exact prime_seventyBP_23
      · exact prime_seventyBP_552015942727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2894771603660389) ^ 1447385801830194 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2894771603660389) ^ 964923867886796 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2894771603660389) ^ 152356400192652 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2894771603660389) ^ 125859634941756 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2894771603660389) ^ 5244 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_3398095891708099 : Nat.Prime 3398095891708099 := by
  apply lucas_primality 3398095891708099 (3 : ZMod 3398095891708099)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (47, 1), (199, 1), (8650384373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (47, 1), (199, 1), (8650384373, 1)] : List FactorBlock).map factorBlockValue).prod) = 3398095891708099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_7
      · exact prime_seventyBP_47
      · exact prime_seventyBP_199
      · exact prime_seventyBP_8650384373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3398095891708099) ^ 1699047945854049 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3398095891708099) ^ 1132698630569366 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3398095891708099) ^ 485442270244014 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3398095891708099) ^ 72299912589534 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3398095891708099) ^ 17075858752302 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3398095891708099) ^ 392826 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_3491813384074819 : Nat.Prime 3491813384074819 := by
  apply lucas_primality 3491813384074819 (2 : ZMod 3491813384074819)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 2), (879089, 1), (1823729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 2), (879089, 1), (1823729, 1)] : List FactorBlock).map factorBlockValue).prod) = 3491813384074819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_11
      · exact prime_seventyBP_879089
      · exact prime_seventyBP_1823729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3491813384074819) ^ 1745906692037409 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3491813384074819) ^ 1163937794691606 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3491813384074819) ^ 317437580370438 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3491813384074819) ^ 3972081762 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3491813384074819) ^ 1914655842 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_4791656170655801 : Nat.Prime 4791656170655801 := by
  apply lucas_primality 4791656170655801 (3 : ZMod 4791656170655801)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (129263, 1), (185345233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (129263, 1), (185345233, 1)] : List FactorBlock).map factorBlockValue).prod) = 4791656170655801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_129263
      · exact prime_seventyBP_185345233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4791656170655801) ^ 2395828085327900 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4791656170655801) ^ 958331234131160 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4791656170655801) ^ 37069046600 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4791656170655801) ^ 25852600 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_7635511036552187 : Nat.Prime 7635511036552187 := by
  apply lucas_primality 7635511036552187 (2 : ZMod 7635511036552187)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (62586156037313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (62586156037313, 1)] : List FactorBlock).map factorBlockValue).prod) = 7635511036552187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_61
      · exact prime_seventyBP_62586156037313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7635511036552187) ^ 3817755518276093 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7635511036552187) ^ 125172312074626 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7635511036552187) ^ 122 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_12575157516465619 : Nat.Prime 12575157516465619 := by
  apply lucas_primality 12575157516465619 (3 : ZMod 12575157516465619)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (211, 1), (431868861751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (211, 1), (431868861751, 1)] : List FactorBlock).map factorBlockValue).prod) = 12575157516465619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_23
      · exact prime_seventyBP_211
      · exact prime_seventyBP_431868861751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12575157516465619) ^ 6287578758232809 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 12575157516465619) ^ 4191719172155206 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 12575157516465619) ^ 546745978976766 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 12575157516465619) ^ 59597902921638 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 12575157516465619) ^ 29118 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_12996947044848869 : Nat.Prime 12996947044848869 := by
  apply lucas_primality 12996947044848869 (2 : ZMod 12996947044848869)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (191, 1), (379, 1), (25969, 1), (42157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (191, 1), (379, 1), (25969, 1), (42157, 1)] : List FactorBlock).map factorBlockValue).prod) = 12996947044848869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_41
      · exact prime_seventyBP_191
      · exact prime_seventyBP_379
      · exact prime_seventyBP_25969
      · exact prime_seventyBP_42157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12996947044848869) ^ 6498473522424434 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 12996947044848869) ^ 316998708410948 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 12996947044848869) ^ 68046843166748 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 12996947044848869) ^ 34292736266092 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 12996947044848869) ^ 500479303972 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 12996947044848869) ^ 308298670324 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_15164470141930597 : Nat.Prime 15164470141930597 := by
  apply lucas_primality 15164470141930597 (2 : ZMod 15164470141930597)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (293, 1), (4312989232631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (293, 1), (4312989232631, 1)] : List FactorBlock).map factorBlockValue).prod) = 15164470141930597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_293
      · exact prime_seventyBP_4312989232631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15164470141930597) ^ 7582235070965298 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 15164470141930597) ^ 5054823380643532 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 15164470141930597) ^ 51755870791572 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 15164470141930597) ^ 3516 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_19858395861400883 : Nat.Prime 19858395861400883 := by
  apply lucas_primality 19858395861400883 (2 : ZMod 19858395861400883)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (102362865264953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (102362865264953, 1)] : List FactorBlock).map factorBlockValue).prod) = 19858395861400883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_97
      · exact prime_seventyBP_102362865264953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19858395861400883) ^ 9929197930700441 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 19858395861400883) ^ 204725730529906 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 19858395861400883) ^ 194 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_35513909464608403 : Nat.Prime 35513909464608403 := by
  apply lucas_primality 35513909464608403 (2 : ZMod 35513909464608403)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (283, 1), (20915141027449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (283, 1), (20915141027449, 1)] : List FactorBlock).map factorBlockValue).prod) = 35513909464608403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_283
      · exact prime_seventyBP_20915141027449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35513909464608403) ^ 17756954732304201 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35513909464608403) ^ 11837969821536134 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35513909464608403) ^ 125490846164694 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35513909464608403) ^ 1698 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_40776333437372021 : Nat.Prime 40776333437372021 := by
  apply lucas_primality 40776333437372021 (3 : ZMod 40776333437372021)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (4426117, 1), (460633253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (4426117, 1), (460633253, 1)] : List FactorBlock).map factorBlockValue).prod) = 40776333437372021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_4426117
      · exact prime_seventyBP_460633253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 40776333437372021) ^ 20388166718686010 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 40776333437372021) ^ 8155266687474404 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 40776333437372021) ^ 9212665060 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 40776333437372021) ^ 88522340 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_52263156742600351 : Nat.Prime 52263156742600351 := by
  apply lucas_primality 52263156742600351 (3 : ZMod 52263156742600351)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (21929, 1), (15888597061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (21929, 1), (15888597061, 1)] : List FactorBlock).map factorBlockValue).prod) = 52263156742600351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_21929
      · exact prime_seventyBP_15888597061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 52263156742600351) ^ 26131578371300175 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52263156742600351) ^ 17421052247533450 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52263156742600351) ^ 10452631348520070 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52263156742600351) ^ 2383289559150 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52263156742600351) ^ 3289350 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_58289802952804223 : Nat.Prime 58289802952804223 := by
  apply lucas_primality 58289802952804223 (5 : ZMod 58289802952804223)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3389, 1), (4363, 1), (1971087073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3389, 1), (4363, 1), (1971087073, 1)] : List FactorBlock).map factorBlockValue).prod) = 58289802952804223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3389
      · exact prime_seventyBP_4363
      · exact prime_seventyBP_1971087073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 58289802952804223) ^ 29144901476402111 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 58289802952804223) ^ 17199705798998 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 58289802952804223) ^ 13360028180794 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 58289802952804223) ^ 29572414 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_61336229903205827 : Nat.Prime 61336229903205827 := by
  apply lucas_primality 61336229903205827 (2 : ZMod 61336229903205827)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1303, 1), (4211, 1), (5589300061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1303, 1), (4211, 1), (5589300061, 1)] : List FactorBlock).map factorBlockValue).prod) = 61336229903205827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_1303
      · exact prime_seventyBP_4211
      · exact prime_seventyBP_5589300061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61336229903205827) ^ 30668114951602913 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 61336229903205827) ^ 47073085113742 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 61336229903205827) ^ 14565715958966 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 61336229903205827) ^ 10973866 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_86710842632149349 : Nat.Prime 86710842632149349 := by
  apply lucas_primality 86710842632149349 (2 : ZMod 86710842632149349)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (747507264070253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (747507264070253, 1)] : List FactorBlock).map factorBlockValue).prod) = 86710842632149349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_29
      · exact prime_seventyBP_747507264070253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 86710842632149349) ^ 43355421316074674 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 86710842632149349) ^ 2990029056281012 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 86710842632149349) ^ 116 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_127160014938533693 : Nat.Prime 127160014938533693 := by
  apply lucas_primality 127160014938533693 (2 : ZMod 127160014938533693)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 2), (29, 1), (491, 1), (7725262513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 2), (29, 1), (491, 1), (7725262513, 1)] : List FactorBlock).map factorBlockValue).prod) = 127160014938533693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_17
      · exact prime_seventyBP_29
      · exact prime_seventyBP_491
      · exact prime_seventyBP_7725262513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 127160014938533693) ^ 63580007469266846 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 127160014938533693) ^ 7480000878737276 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 127160014938533693) ^ 4384828101328748 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 127160014938533693) ^ 258981700485812 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 127160014938533693) ^ 16460284 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_135923835668323961 : Nat.Prime 135923835668323961 := by
  apply lucas_primality 135923835668323961 (3 : ZMod 135923835668323961)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (3398095891708099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (3398095891708099, 1)] : List FactorBlock).map factorBlockValue).prod) = 135923835668323961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_3398095891708099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 135923835668323961) ^ 67961917834161980 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 135923835668323961) ^ 27184767133664792 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 135923835668323961) ^ 40 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_341583049231925903 : Nat.Prime 341583049231925903 := by
  apply lucas_primality 341583049231925903 (5 : ZMod 341583049231925903)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (2894771603660389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (2894771603660389, 1)] : List FactorBlock).map factorBlockValue).prod) = 341583049231925903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_59
      · exact prime_seventyBP_2894771603660389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 341583049231925903) ^ 170791524615962951 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 341583049231925903) ^ 5789543207320778 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 341583049231925903) ^ 118 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_407595466465985099 : Nat.Prime 407595466465985099 := by
  apply lucas_primality 407595466465985099 (2 : ZMod 407595466465985099)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (3607237, 1), (8070986711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (3607237, 1), (8070986711, 1)] : List FactorBlock).map factorBlockValue).prod) = 407595466465985099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_3607237
      · exact prime_seventyBP_8070986711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 407595466465985099) ^ 203797733232992549 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 407595466465985099) ^ 58227923780855014 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 407595466465985099) ^ 112993813954 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 407595466465985099) ^ 50501318 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_465816106770417863 : Nat.Prime 465816106770417863 := by
  apply lucas_primality 465816106770417863 (5 : ZMod 465816106770417863)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (347, 1), (671204764798873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (347, 1), (671204764798873, 1)] : List FactorBlock).map factorBlockValue).prod) = 465816106770417863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_347
      · exact prime_seventyBP_671204764798873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 465816106770417863) ^ 232908053385208931 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 465816106770417863) ^ 1342409529597746 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 465816106770417863) ^ 694 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_542304476636213279 : Nat.Prime 542304476636213279 := by
  apply lucas_primality 542304476636213279 (7 : ZMod 542304476636213279)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (53, 1), (1166141, 1), (337476011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (53, 1), (1166141, 1), (337476011, 1)] : List FactorBlock).map factorBlockValue).prod) = 542304476636213279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_13
      · exact prime_seventyBP_53
      · exact prime_seventyBP_1166141
      · exact prime_seventyBP_337476011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 542304476636213279) ^ 271152238318106639 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 542304476636213279) ^ 41715728972016406 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 542304476636213279) ^ 10232159936532326 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 542304476636213279) ^ 465041943158 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 542304476636213279) ^ 1606942298 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_720321023399680961 : Nat.Prime 720321023399680961 := by
  apply lucas_primality 720321023399680961 (3 : ZMod 720321023399680961)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (23, 1), (317, 1), (308737237433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (23, 1), (317, 1), (308737237433, 1)] : List FactorBlock).map factorBlockValue).prod) = 720321023399680961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_23
      · exact prime_seventyBP_317
      · exact prime_seventyBP_308737237433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 720321023399680961) ^ 360160511699840480 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 720321023399680961) ^ 144064204679936192 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 720321023399680961) ^ 31318305365203520 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 720321023399680961) ^ 2272306067506880 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 720321023399680961) ^ 2333120 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_727894566812668657 : Nat.Prime 727894566812668657 := by
  apply lucas_primality 727894566812668657 (10 : ZMod 727894566812668657)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (15164470141930597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (15164470141930597, 1)] : List FactorBlock).map factorBlockValue).prod) = 727894566812668657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_15164470141930597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 727894566812668657) ^ 363947283406334328 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 727894566812668657) ^ 242631522270889552 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 727894566812668657) ^ 48 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1173126945766296863 : Nat.Prime 1173126945766296863 := by
  apply lucas_primality 1173126945766296863 (5 : ZMod 1173126945766296863)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (167, 1), (19469, 1), (26203, 1), (625909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (167, 1), (19469, 1), (26203, 1), (625909, 1)] : List FactorBlock).map factorBlockValue).prod) = 1173126945766296863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_11
      · exact prime_seventyBP_167
      · exact prime_seventyBP_19469
      · exact prime_seventyBP_26203
      · exact prime_seventyBP_625909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1173126945766296863) ^ 586563472883148431 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1173126945766296863) ^ 106647904160572442 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1173126945766296863) ^ 7024712250097586 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1173126945766296863) ^ 60256148018198 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1173126945766296863) ^ 44770711207354 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1173126945766296863) ^ 1874277164518 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1461084005468213309 : Nat.Prime 1461084005468213309 := by
  apply lucas_primality 1461084005468213309 (2 : ZMod 1461084005468213309)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (43, 1), (83, 1), (101, 1), (179, 1), (62208947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (43, 1), (83, 1), (101, 1), (179, 1), (62208947, 1)] : List FactorBlock).map factorBlockValue).prod) = 1461084005468213309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_13
      · exact prime_seventyBP_43
      · exact prime_seventyBP_83
      · exact prime_seventyBP_101
      · exact prime_seventyBP_179
      · exact prime_seventyBP_62208947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1461084005468213309) ^ 730542002734106654 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1461084005468213309) ^ 208726286495459044 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1461084005468213309) ^ 112391077343708716 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1461084005468213309) ^ 33978697801586356 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1461084005468213309) ^ 17603421752629076 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1461084005468213309) ^ 14466178271962508 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1461084005468213309) ^ 8162480477476052 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1461084005468213309) ^ 23486718164 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1583093613470951651 : Nat.Prime 1583093613470951651 := by
  apply lucas_primality 1583093613470951651 (2 : ZMod 1583093613470951651)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (89, 1), (14489, 1), (24553204073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (89, 1), (14489, 1), (24553204073, 1)] : List FactorBlock).map factorBlockValue).prod) = 1583093613470951651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_89
      · exact prime_seventyBP_14489
      · exact prime_seventyBP_24553204073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1583093613470951651) ^ 791546806735475825 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1583093613470951651) ^ 316618722694190330 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1583093613470951651) ^ 17787568690684850 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1583093613470951651) ^ 109261758124850 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1583093613470951651) ^ 64476050 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_2581441404682826513 : Nat.Prime 2581441404682826513 := by
  apply lucas_primality 2581441404682826513 (3 : ZMod 2581441404682826513)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (636283, 1), (253566554179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (636283, 1), (253566554179, 1)] : List FactorBlock).map factorBlockValue).prod) = 2581441404682826513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_636283
      · exact prime_seventyBP_253566554179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2581441404682826513) ^ 1290720702341413256 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2581441404682826513) ^ 4057064866864 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2581441404682826513) ^ 10180528 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_5400125749137691937 : Nat.Prime 5400125749137691937 := by
  apply lucas_primality 5400125749137691937 (3 : ZMod 5400125749137691937)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (13, 1), (39667, 1), (46750164809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (13, 1), (39667, 1), (46750164809, 1)] : List FactorBlock).map factorBlockValue).prod) = 5400125749137691937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_13
      · exact prime_seventyBP_39667
      · exact prime_seventyBP_46750164809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5400125749137691937) ^ 2700062874568845968 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5400125749137691937) ^ 771446535591098848 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5400125749137691937) ^ 415394288395207072 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5400125749137691937) ^ 136136479923808 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5400125749137691937) ^ 115510304 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_5595821083469205409 : Nat.Prime 5595821083469205409 := by
  apply lucas_primality 5595821083469205409 (11 : ZMod 5595821083469205409)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (58289802952804223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (58289802952804223, 1)] : List FactorBlock).map factorBlockValue).prod) = 5595821083469205409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_58289802952804223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 5595821083469205409) ^ 2797910541734602704 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 5595821083469205409) ^ 1865273694489735136 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 5595821083469205409) ^ 96 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_7326394580700149261 : Nat.Prime 7326394580700149261 := by
  apply lucas_primality 7326394580700149261 (2 : ZMod 7326394580700149261)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (151, 1), (142703439437089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (151, 1), (142703439437089, 1)] : List FactorBlock).map factorBlockValue).prod) = 7326394580700149261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_17
      · exact prime_seventyBP_151
      · exact prime_seventyBP_142703439437089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7326394580700149261) ^ 3663197290350074630 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7326394580700149261) ^ 1465278916140029852 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7326394580700149261) ^ 430964387100008780 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7326394580700149261) ^ 48519169408610260 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7326394580700149261) ^ 51340 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_7702653292189832477 : Nat.Prime 7702653292189832477 := by
  apply lucas_primality 7702653292189832477 (2 : ZMod 7702653292189832477)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41269, 1), (46661254768651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41269, 1), (46661254768651, 1)] : List FactorBlock).map factorBlockValue).prod) = 7702653292189832477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_41269
      · exact prime_seventyBP_46661254768651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7702653292189832477) ^ 3851326646094916238 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7702653292189832477) ^ 186645019074604 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7702653292189832477) ^ 165076 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_9361897501253692151 : Nat.Prime 9361897501253692151 := by
  apply lucas_primality 9361897501253692151 (7 : ZMod 9361897501253692151)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (19, 1), (1407804135526871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (19, 1), (1407804135526871, 1)] : List FactorBlock).map factorBlockValue).prod) = 9361897501253692151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_7
      · exact prime_seventyBP_19
      · exact prime_seventyBP_1407804135526871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 9361897501253692151) ^ 4680948750626846075 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 9361897501253692151) ^ 1872379500250738430 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 9361897501253692151) ^ 1337413928750527450 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 9361897501253692151) ^ 492731447434404850 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 9361897501253692151) ^ 6650 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_11688672043745706473 : Nat.Prime 11688672043745706473 := by
  apply lucas_primality 11688672043745706473 (3 : ZMod 11688672043745706473)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1461084005468213309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1461084005468213309, 1)] : List FactorBlock).map factorBlockValue).prod) = 11688672043745706473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_1461084005468213309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 11688672043745706473) ^ 5844336021872853236 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 11688672043745706473) ^ 8 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_12878185652596527223 : Nat.Prime 12878185652596527223 := by
  apply lucas_primality 12878185652596527223 (11 : ZMod 12878185652596527223)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (173, 1), (179, 1), (69311340311711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (173, 1), (179, 1), (69311340311711, 1)] : List FactorBlock).map factorBlockValue).prod) = 12878185652596527223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_173
      · exact prime_seventyBP_179
      · exact prime_seventyBP_69311340311711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 12878185652596527223) ^ 6439092826298263611 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 12878185652596527223) ^ 4292728550865509074 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 12878185652596527223) ^ 74440379494777614 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 12878185652596527223) ^ 71945171243556018 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 12878185652596527223) ^ 185802 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_30742029421407055649 : Nat.Prime 30742029421407055649 := by
  apply lucas_primality 30742029421407055649 (3 : ZMod 30742029421407055649)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 2), (19, 1), (41, 1), (13339, 1), (547060201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 2), (19, 1), (41, 1), (13339, 1), (547060201, 1)] : List FactorBlock).map factorBlockValue).prod) = 30742029421407055649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_13
      · exact prime_seventyBP_19
      · exact prime_seventyBP_41
      · exact prime_seventyBP_13339
      · exact prime_seventyBP_547060201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30742029421407055649) ^ 15371014710703527824 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 30742029421407055649) ^ 2364771493954388896 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 30742029421407055649) ^ 1618001548495108192 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 30742029421407055649) ^ 749805595644074528 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 30742029421407055649) ^ 2304672720699232 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 30742029421407055649) ^ 56194966048 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_31792446384346837723 : Nat.Prime 31792446384346837723 := by
  apply lucas_primality 31792446384346837723 (3 : ZMod 31792446384346837723)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (407595466465985099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (407595466465985099, 1)] : List FactorBlock).map factorBlockValue).prod) = 31792446384346837723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_13
      · exact prime_seventyBP_407595466465985099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31792446384346837723) ^ 15896223192173418861 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 31792446384346837723) ^ 10597482128115612574 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 31792446384346837723) ^ 2445572798795910594 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 31792446384346837723) ^ 78 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_34736492790707656309 : Nat.Prime 34736492790707656309 := by
  apply lucas_primality 34736492790707656309 (6 : ZMod 34736492790707656309)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (12263, 1), (18097, 1), (303342283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (12263, 1), (18097, 1), (303342283, 1)] : List FactorBlock).map factorBlockValue).prod) = 34736492790707656309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_43
      · exact prime_seventyBP_12263
      · exact prime_seventyBP_18097
      · exact prime_seventyBP_303342283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 34736492790707656309) ^ 17368246395353828154 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 34736492790707656309) ^ 11578830930235885436 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 34736492790707656309) ^ 807825413737387356 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 34736492790707656309) ^ 2832626012452716 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 34736492790707656309) ^ 1919461390877364 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 34736492790707656309) ^ 114512531676 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_61484058842814111299 : Nat.Prime 61484058842814111299 := by
  apply lucas_primality 61484058842814111299 (2 : ZMod 61484058842814111299)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (30742029421407055649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (30742029421407055649, 1)] : List FactorBlock).map factorBlockValue).prod) = 61484058842814111299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_30742029421407055649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 61484058842814111299) ^ 30742029421407055649 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 61484058842814111299) ^ 2 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_62183193205238520601 : Nat.Prime 62183193205238520601 := by
  apply lucas_primality 62183193205238520601 (23 : ZMod 62183193205238520601)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (41, 1), (73, 1), (3643, 1), (9505082299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (41, 1), (73, 1), (3643, 1), (9505082299, 1)] : List FactorBlock).map factorBlockValue).prod) = 62183193205238520601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_41
      · exact prime_seventyBP_73
      · exact prime_seventyBP_3643
      · exact prime_seventyBP_9505082299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 62183193205238520601) ^ 31091596602619260300 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (23 : ZMod 62183193205238520601) ^ 20727731068412840200 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (23 : ZMod 62183193205238520601) ^ 12436638641047704120 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (23 : ZMod 62183193205238520601) ^ 1516663248908256600 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (23 : ZMod 62183193205238520601) ^ 851824564455322200 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (23 : ZMod 62183193205238520601) ^ 17069226792544200 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (23 : ZMod 62183193205238520601) ^ 6542099400 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_72279228440482697149 : Nat.Prime 72279228440482697149 := by
  apply lucas_primality 72279228440482697149 (6 : ZMod 72279228440482697149)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (647, 1), (653, 1), (59951, 1), (3549307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (647, 1), (653, 1), (59951, 1), (3549307, 1)] : List FactorBlock).map factorBlockValue).prod) = 72279228440482697149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_67
      · exact prime_seventyBP_647
      · exact prime_seventyBP_653
      · exact prime_seventyBP_59951
      · exact prime_seventyBP_3549307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 72279228440482697149) ^ 36139614220241348574 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 72279228440482697149) ^ 24093076146827565716 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 72279228440482697149) ^ 1078794454335562644 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 72279228440482697149) ^ 111714417991472484 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 72279228440482697149) ^ 110687945544383916 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 72279228440482697149) ^ 1205638412044548 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 72279228440482697149) ^ 20364321384564 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_120481699105749015631 : Nat.Prime 120481699105749015631 := by
  apply lucas_primality 120481699105749015631 (3 : ZMod 120481699105749015631)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (103, 1), (12996947044848869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (103, 1), (12996947044848869, 1)] : List FactorBlock).map factorBlockValue).prod) = 120481699105749015631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_103
      · exact prime_seventyBP_12996947044848869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 120481699105749015631) ^ 60240849552874507815 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 120481699105749015631) ^ 40160566368583005210 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 120481699105749015631) ^ 24096339821149803126 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 120481699105749015631) ^ 1169725234036398210 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 120481699105749015631) ^ 9270 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_186818852912162143301 : Nat.Prime 186818852912162143301 := by
  apply lucas_primality 186818852912162143301 (2 : ZMod 186818852912162143301)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (19, 1), (149, 1), (1621, 1), (4993, 1), (81533531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (19, 1), (149, 1), (1621, 1), (4993, 1), (81533531, 1)] : List FactorBlock).map factorBlockValue).prod) = 186818852912162143301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_19
      · exact prime_seventyBP_149
      · exact prime_seventyBP_1621
      · exact prime_seventyBP_4993
      · exact prime_seventyBP_81533531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 186818852912162143301) ^ 93409426456081071650 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 186818852912162143301) ^ 37363770582432428660 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 186818852912162143301) ^ 9832571205903270700 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 186818852912162143301) ^ 1253817804779611700 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 186818852912162143301) ^ 115249138132117300 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 186818852912162143301) ^ 37416153196908100 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 186818852912162143301) ^ 2291313164300 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_492062844532405986173 : Nat.Prime 492062844532405986173 := by
  apply lucas_primality 492062844532405986173 (2 : ZMod 492062844532405986173)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (397, 1), (15373, 1), (20156329423303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (397, 1), (15373, 1), (20156329423303, 1)] : List FactorBlock).map factorBlockValue).prod) = 492062844532405986173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_397
      · exact prime_seventyBP_15373
      · exact prime_seventyBP_20156329423303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 492062844532405986173) ^ 246031422266202993086 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 492062844532405986173) ^ 1239453008897748076 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 492062844532405986173) ^ 32008251124205164 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 492062844532405986173) ^ 24412324 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1080386555401235048311 : Nat.Prime 1080386555401235048311 := by
  apply lucas_primality 1080386555401235048311 (3 : ZMod 1080386555401235048311)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (869371, 1), (13808023341029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (869371, 1), (13808023341029, 1)] : List FactorBlock).map factorBlockValue).prod) = 1080386555401235048311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_869371
      · exact prime_seventyBP_13808023341029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1080386555401235048311) ^ 540193277700617524155 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1080386555401235048311) ^ 360128851800411682770 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1080386555401235048311) ^ 216077311080247009662 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1080386555401235048311) ^ 1242722100692610 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1080386555401235048311) ^ 78243390 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1152492150606852801929 : Nat.Prime 1152492150606852801929 := by
  apply lucas_primality 1152492150606852801929 (3 : ZMod 1152492150606852801929)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13, 1), (1583093613470951651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13, 1), (1583093613470951651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1152492150606852801929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_13
      · exact prime_seventyBP_1583093613470951651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1152492150606852801929) ^ 576246075303426400964 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1152492150606852801929) ^ 164641735800978971704 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1152492150606852801929) ^ 88653242354373292456 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1152492150606852801929) ^ 728 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1159036708733687450071 : Nat.Prime 1159036708733687450071 := by
  apply lucas_primality 1159036708733687450071 (3 : ZMod 1159036708733687450071)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (12878185652596527223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (12878185652596527223, 1)] : List FactorBlock).map factorBlockValue).prod) = 1159036708733687450071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_12878185652596527223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1159036708733687450071) ^ 579518354366843725035 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1159036708733687450071) ^ 386345569577895816690 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1159036708733687450071) ^ 231807341746737490014 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1159036708733687450071) ^ 90 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1245487078719025374371 : Nat.Prime 1245487078719025374371 := by
  apply lucas_primality 1245487078719025374371 (2 : ZMod 1245487078719025374371)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (7326394580700149261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (7326394580700149261, 1)] : List FactorBlock).map factorBlockValue).prod) = 1245487078719025374371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_17
      · exact prime_seventyBP_7326394580700149261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1245487078719025374371) ^ 622743539359512687185 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1245487078719025374371) ^ 249097415743805074874 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1245487078719025374371) ^ 73263945807001492610 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1245487078719025374371) ^ 170 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1470096565658639645647 : Nat.Prime 1470096565658639645647 := by
  apply lucas_primality 1470096565658639645647 (6 : ZMod 1470096565658639645647)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (7607, 1), (6323003, 1), (96112957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (7607, 1), (6323003, 1), (96112957, 1)] : List FactorBlock).map factorBlockValue).prod) = 1470096565658639645647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_53
      · exact prime_seventyBP_7607
      · exact prime_seventyBP_6323003
      · exact prime_seventyBP_96112957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1470096565658639645647) ^ 735048282829319822823 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1470096565658639645647) ^ 490032188552879881882 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1470096565658639645647) ^ 27737671050163012182 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1470096565658639645647) ^ 193255759913058978 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1470096565658639645647) ^ 232499741919882 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1470096565658639645647) ^ 15295508655078 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1770346427984633480381 : Nat.Prime 1770346427984633480381 := by
  apply lucas_primality 1770346427984633480381 (2 : ZMod 1770346427984633480381)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (19, 1), (673271, 1), (988522853233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (19, 1), (673271, 1), (988522853233, 1)] : List FactorBlock).map factorBlockValue).prod) = 1770346427984633480381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_7
      · exact prime_seventyBP_19
      · exact prime_seventyBP_673271
      · exact prime_seventyBP_988522853233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1770346427984633480381) ^ 885173213992316740190 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1770346427984633480381) ^ 354069285596926696076 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1770346427984633480381) ^ 252906632569233354340 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1770346427984633480381) ^ 93176127788664920020 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1770346427984633480381) ^ 2629470789599780 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1770346427984633480381) ^ 1790900860 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_2029669649012328102889 : Nat.Prime 2029669649012328102889 := by
  apply lucas_primality 2029669649012328102889 (11 : ZMod 2029669649012328102889)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 2), (197, 1), (1627, 1), (730891876193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 2), (197, 1), (1627, 1), (730891876193, 1)] : List FactorBlock).map factorBlockValue).prod) = 2029669649012328102889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_19
      · exact prime_seventyBP_197
      · exact prime_seventyBP_1627
      · exact prime_seventyBP_730891876193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2029669649012328102889) ^ 1014834824506164051444 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 2029669649012328102889) ^ 676556549670776034296 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 2029669649012328102889) ^ 106824718369069900152 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 2029669649012328102889) ^ 10302891619351919304 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 2029669649012328102889) ^ 1247492101421221944 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 2029669649012328102889) ^ 2776976616 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_2126285429826030873709 : Nat.Prime 2126285429826030873709 := by
  apply lucas_primality 2126285429826030873709 (2 : ZMod 2126285429826030873709)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (73, 1), (17923, 1), (65293, 1), (26937011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (73, 1), (17923, 1), (65293, 1), (26937011, 1)] : List FactorBlock).map factorBlockValue).prod) = 2126285429826030873709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_7
      · exact prime_seventyBP_11
      · exact prime_seventyBP_73
      · exact prime_seventyBP_17923
      · exact prime_seventyBP_65293
      · exact prime_seventyBP_26937011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2126285429826030873709) ^ 1063142714913015436854 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2126285429826030873709) ^ 708761809942010291236 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2126285429826030873709) ^ 303755061403718696244 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2126285429826030873709) ^ 193298675438730079428 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2126285429826030873709) ^ 29127197668849737996 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2126285429826030873709) ^ 118634460181109796 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2126285429826030873709) ^ 32565289232016156 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2126285429826030873709) ^ 78935462803428 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_3113120389668276719951 : Nat.Prime 3113120389668276719951 := by
  apply lucas_primality 3113120389668276719951 (13 : ZMod 3113120389668276719951)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (5793360847, 1), (10747200017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (5793360847, 1), (10747200017, 1)] : List FactorBlock).map factorBlockValue).prod) = 3113120389668276719951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_5793360847
      · exact prime_seventyBP_10747200017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 3113120389668276719951) ^ 1556560194834138359975 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 3113120389668276719951) ^ 622624077933655343990 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 3113120389668276719951) ^ 537360000850 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 3113120389668276719951) ^ 289668042350 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_3585371515658396110139 : Nat.Prime 3585371515658396110139 := by
  apply lucas_primality 3585371515658396110139 (2 : ZMod 3585371515658396110139)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (421, 1), (166631, 1), (1344970227301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (421, 1), (166631, 1), (1344970227301, 1)] : List FactorBlock).map factorBlockValue).prod) = 3585371515658396110139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_19
      · exact prime_seventyBP_421
      · exact prime_seventyBP_166631
      · exact prime_seventyBP_1344970227301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3585371515658396110139) ^ 1792685757829198055069 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3585371515658396110139) ^ 188703763982020847902 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3585371515658396110139) ^ 8516321889924931378 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3585371515658396110139) ^ 21516833696361398 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3585371515658396110139) ^ 2665762738 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_13983118593839111947291 : Nat.Prime 13983118593839111947291 := by
  apply lucas_primality 13983118593839111947291 (2 : ZMod 13983118593839111947291)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2021009, 1), (230629330759027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2021009, 1), (230629330759027, 1)] : List FactorBlock).map factorBlockValue).prod) = 13983118593839111947291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_2021009
      · exact prime_seventyBP_230629330759027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13983118593839111947291) ^ 6991559296919555973645 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13983118593839111947291) ^ 4661039531279703982430 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13983118593839111947291) ^ 2796623718767822389458 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13983118593839111947291) ^ 6918879922770810 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13983118593839111947291) ^ 60630270 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_15513841747895224548589 : Nat.Prime 15513841747895224548589 := by
  apply lucas_primality 15513841747895224548589 (6 : ZMod 15513841747895224548589)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1301, 1), (789227, 1), (1259096103887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1301, 1), (789227, 1), (1259096103887, 1)] : List FactorBlock).map factorBlockValue).prod) = 15513841747895224548589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_1301
      · exact prime_seventyBP_789227
      · exact prime_seventyBP_1259096103887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 15513841747895224548589) ^ 7756920873947612274294 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 15513841747895224548589) ^ 5171280582631741516196 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 15513841747895224548589) ^ 11924551689389104188 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 15513841747895224548589) ^ 19657008373883844 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 15513841747895224548589) ^ 12321411924 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_17286184886419760772977 : Nat.Prime 17286184886419760772977 := by
  apply lucas_primality 17286184886419760772977 (3 : ZMod 17286184886419760772977)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1080386555401235048311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1080386555401235048311, 1)] : List FactorBlock).map factorBlockValue).prod) = 17286184886419760772977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_1080386555401235048311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 17286184886419760772977) ^ 8643092443209880386488 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 17286184886419760772977) ^ 16 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_45690111592089214580101 : Nat.Prime 45690111592089214580101 := by
  apply lucas_primality 45690111592089214580101 (11 : ZMod 45690111592089214580101)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (73, 1), (63073, 1), (1148879, 1), (9597079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (73, 1), (63073, 1), (1148879, 1), (9597079, 1)] : List FactorBlock).map factorBlockValue).prod) = 45690111592089214580101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_73
      · exact prime_seventyBP_63073
      · exact prime_seventyBP_1148879
      · exact prime_seventyBP_9597079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 45690111592089214580101) ^ 22845055796044607290050 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 45690111592089214580101) ^ 15230037197363071526700 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 45690111592089214580101) ^ 9138022318417842916020 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 45690111592089214580101) ^ 625891939617660473700 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 45690111592089214580101) ^ 724400481855773700 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 45690111592089214580101) ^ 39769298239491900 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 45690111592089214580101) ^ 4760835207471900 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_46702991605177118513717 : Nat.Prime 46702991605177118513717 := by
  apply lucas_primality 46702991605177118513717 (2 : ZMod 46702991605177118513717)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1627, 1), (615226291, 1), (11664396397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1627, 1), (615226291, 1), (11664396397, 1)] : List FactorBlock).map factorBlockValue).prod) = 46702991605177118513717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_1627
      · exact prime_seventyBP_615226291
      · exact prime_seventyBP_11664396397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46702991605177118513717) ^ 23351495802588559256858 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46702991605177118513717) ^ 28704973328320294108 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46702991605177118513717) ^ 75911891751676 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46702991605177118513717) ^ 4003892701828 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_68131693092292551682693 : Nat.Prime 68131693092292551682693 := by
  apply lucas_primality 68131693092292551682693 (5 : ZMod 68131693092292551682693)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (40589599, 1), (4512232619339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (40589599, 1), (4512232619339, 1)] : List FactorBlock).map factorBlockValue).prod) = 68131693092292551682693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_31
      · exact prime_seventyBP_40589599
      · exact prime_seventyBP_4512232619339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 68131693092292551682693) ^ 34065846546146275841346 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 68131693092292551682693) ^ 22710564364097517227564 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 68131693092292551682693) ^ 2197796551364275860732 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 68131693092292551682693) ^ 1678550534394108 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 68131693092292551682693) ^ 15099330828 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_83254629716418266338373 : Nat.Prime 83254629716418266338373 := by
  apply lucas_primality 83254629716418266338373 (2 : ZMod 83254629716418266338373)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (4144711, 1), (717391304901409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (4144711, 1), (717391304901409, 1)] : List FactorBlock).map factorBlockValue).prod) = 83254629716418266338373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_4144711
      · exact prime_seventyBP_717391304901409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 83254629716418266338373) ^ 41627314858209133169186 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 83254629716418266338373) ^ 11893518530916895191196 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 83254629716418266338373) ^ 20086956537239452 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 83254629716418266338373) ^ 116051908 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_91292625198089799051313 : Nat.Prime 91292625198089799051313 := by
  apply lucas_primality 91292625198089799051313 (5 : ZMod 91292625198089799051313)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (30463957, 1), (2312301072071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (30463957, 1), (2312301072071, 1)] : List FactorBlock).map factorBlockValue).prod) = 91292625198089799051313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_30463957
      · exact prime_seventyBP_2312301072071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 91292625198089799051313) ^ 45646312599044899525656 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 91292625198089799051313) ^ 30430875066029933017104 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 91292625198089799051313) ^ 2996742189404016 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 91292625198089799051313) ^ 39481288272 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_342337337069476072926937 : Nat.Prime 342337337069476072926937 := by
  apply lucas_primality 342337337069476072926937 (5 : ZMod 342337337069476072926937)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (53, 1), (71, 1), (839, 1), (14699, 1), (69463, 1), (4424921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (53, 1), (71, 1), (839, 1), (14699, 1), (69463, 1), (4424921, 1)] : List FactorBlock).map factorBlockValue).prod) = 342337337069476072926937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_53
      · exact prime_seventyBP_71
      · exact prime_seventyBP_839
      · exact prime_seventyBP_14699
      · exact prime_seventyBP_69463
      · exact prime_seventyBP_4424921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 342337337069476072926937) ^ 171168668534738036463468 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 342337337069476072926937) ^ 114112445689825357642312 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 342337337069476072926937) ^ 6459195039046718357112 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 342337337069476072926937) ^ 4821652634781353139816 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 342337337069476072926937) ^ 408030199129292101224 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 342337337069476072926937) ^ 23289838565172873864 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 342337337069476072926937) ^ 4928340801138391272 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 342337337069476072926937) ^ 77365751178264216 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_957633440027743146560927 : Nat.Prime 957633440027743146560927 := by
  apply lucas_primality 957633440027743146560927 (10 : ZMod 957633440027743146560927)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (233, 1), (186818852912162143301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (233, 1), (186818852912162143301, 1)] : List FactorBlock).map factorBlockValue).prod) = 957633440027743146560927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_11
      · exact prime_seventyBP_233
      · exact prime_seventyBP_186818852912162143301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 957633440027743146560927) ^ 478816720013871573280463 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 957633440027743146560927) ^ 87057585457067558778266 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 957633440027743146560927) ^ 4110014764067567152622 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (10 : ZMod 957633440027743146560927) ^ 5126 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1235757531539458902878831 : Nat.Prime 1235757531539458902878831 := by
  apply lucas_primality 1235757531539458902878831 (11 : ZMod 1235757531539458902878831)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1481796791, 1), (83395883905613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1481796791, 1), (83395883905613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1235757531539458902878831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_1481796791
      · exact prime_seventyBP_83395883905613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1235757531539458902878831) ^ 617878765769729451439415 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 1235757531539458902878831) ^ 247151506307891780575766 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 1235757531539458902878831) ^ 833958839056130 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 1235757531539458902878831) ^ 14817967910 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1333011434301874278812501 : Nat.Prime 1333011434301874278812501 := by
  apply lucas_primality 1333011434301874278812501 (2 : ZMod 1333011434301874278812501)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 6), (941, 1), (1453, 1), (15599066864357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 6), (941, 1), (1453, 1), (15599066864357, 1)] : List FactorBlock).map factorBlockValue).prod) = 1333011434301874278812501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_941
      · exact prime_seventyBP_1453
      · exact prime_seventyBP_15599066864357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1333011434301874278812501) ^ 666505717150937139406250 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1333011434301874278812501) ^ 266602286860374855762500 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1333011434301874278812501) ^ 1416590259619420062500 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1333011434301874278812501) ^ 917420119959996062500 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1333011434301874278812501) ^ 85454562500 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1517672508476023523304517 : Nat.Prime 1517672508476023523304517 := by
  apply lucas_primality 1517672508476023523304517 (2 : ZMod 1517672508476023523304517)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 2), (17, 1), (61484058842814111299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 2), (17, 1), (61484058842814111299, 1)] : List FactorBlock).map factorBlockValue).prod) = 1517672508476023523304517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_11
      · exact prime_seventyBP_17
      · exact prime_seventyBP_61484058842814111299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1517672508476023523304517) ^ 758836254238011761652258 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1517672508476023523304517) ^ 505890836158674507768172 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1517672508476023523304517) ^ 137970228043274865754956 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1517672508476023523304517) ^ 89274853439766089606148 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1517672508476023523304517) ^ 24684 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1644844017315211724883637 : Nat.Prime 1644844017315211724883637 := by
  apply lucas_primality 1644844017315211724883637 (2 : ZMod 1644844017315211724883637)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (45690111592089214580101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (45690111592089214580101, 1)] : List FactorBlock).map factorBlockValue).prod) = 1644844017315211724883637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_45690111592089214580101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1644844017315211724883637) ^ 822422008657605862441818 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1644844017315211724883637) ^ 548281339105070574961212 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1644844017315211724883637) ^ 36 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_5172417617949847670362207 : Nat.Prime 5172417617949847670362207 := by
  apply lucas_primality 5172417617949847670362207 (3 : ZMod 5172417617949847670362207)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (616312744121, 1), (1398753491981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (616312744121, 1), (1398753491981, 1)] : List FactorBlock).map factorBlockValue).prod) = 5172417617949847670362207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_616312744121
      · exact prime_seventyBP_1398753491981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5172417617949847670362207) ^ 2586208808974923835181103 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5172417617949847670362207) ^ 1724139205983282556787402 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5172417617949847670362207) ^ 8392520951886 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5172417617949847670362207) ^ 3697876464726 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_8037164405865549453801623 : Nat.Prime 8037164405865549453801623 := by
  apply lucas_primality 8037164405865549453801623 (5 : ZMod 8037164405865549453801623)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1709, 1), (2156849, 1), (1090212237000071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1709, 1), (2156849, 1), (1090212237000071, 1)] : List FactorBlock).map factorBlockValue).prod) = 8037164405865549453801623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_1709
      · exact prime_seventyBP_2156849
      · exact prime_seventyBP_1090212237000071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 8037164405865549453801623) ^ 4018582202932774726900811 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 8037164405865549453801623) ^ 4702846346322732272558 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 8037164405865549453801623) ^ 3726345426066242678 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 8037164405865549453801623) ^ 7372109882 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_8177735364347585249584517 : Nat.Prime 8177735364347585249584517 := by
  apply lucas_primality 8177735364347585249584517 (2 : ZMod 8177735364347585249584517)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (431, 1), (4507, 1), (93992141, 1), (11197387057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (431, 1), (4507, 1), (93992141, 1), (11197387057, 1)] : List FactorBlock).map factorBlockValue).prod) = 8177735364347585249584517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_431
      · exact prime_seventyBP_4507
      · exact prime_seventyBP_93992141
      · exact prime_seventyBP_11197387057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8177735364347585249584517) ^ 4088867682173792624792258 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8177735364347585249584517) ^ 18973863954402749999036 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8177735364347585249584517) ^ 1814452044452537219788 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8177735364347585249584517) ^ 87004458855209876 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8177735364347585249584517) ^ 730325327035588 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_16154339622720586126448431 : Nat.Prime 16154339622720586126448431 := by
  apply lucas_primality 16154339622720586126448431 (3 : ZMod 16154339622720586126448431)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (5647, 1), (61129, 1), (42160053301651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (5647, 1), (61129, 1), (42160053301651, 1)] : List FactorBlock).map factorBlockValue).prod) = 16154339622720586126448431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_37
      · exact prime_seventyBP_5647
      · exact prime_seventyBP_61129
      · exact prime_seventyBP_42160053301651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16154339622720586126448431) ^ 8077169811360293063224215 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 16154339622720586126448431) ^ 5384779874240195375482810 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 16154339622720586126448431) ^ 3230867924544117225289686 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 16154339622720586126448431) ^ 436603773587042868282390 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 16154339622720586126448431) ^ 2860694107087052616690 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 16154339622720586126448431) ^ 264266381303809748670 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 16154339622720586126448431) ^ 383166963930 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_17430219437067725932138861 : Nat.Prime 17430219437067725932138861 := by
  apply lucas_primality 17430219437067725932138861 (13 : ZMod 17430219437067725932138861)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (29, 1), (157, 1), (650517619, 1), (32694419861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (29, 1), (157, 1), (650517619, 1), (32694419861, 1)] : List FactorBlock).map factorBlockValue).prod) = 17430219437067725932138861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_29
      · exact prime_seventyBP_157
      · exact prime_seventyBP_650517619
      · exact prime_seventyBP_32694419861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 17430219437067725932138861) ^ 8715109718533862966069430 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 17430219437067725932138861) ^ 5810073145689241977379620 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 17430219437067725932138861) ^ 3486043887413545186427772 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 17430219437067725932138861) ^ 601042049554059514901340 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 17430219437067725932138861) ^ 111020505968584241605980 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 17430219437067725932138861) ^ 26794384852883940 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (13 : ZMod 17430219437067725932138861) ^ 533125209475260 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_18285170545116562687979521 : Nat.Prime 18285170545116562687979521 := by
  apply lucas_primality 18285170545116562687979521 (11 : ZMod 18285170545116562687979521)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 12), (3, 1), (5, 1), (281423, 1), (322079, 1), (3283415249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 12), (3, 1), (5, 1), (281423, 1), (322079, 1), (3283415249, 1)] : List FactorBlock).map factorBlockValue).prod) = 18285170545116562687979521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_281423
      · exact prime_seventyBP_322079
      · exact prime_seventyBP_3283415249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 18285170545116562687979521) ^ 9142585272558281343989760 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 18285170545116562687979521) ^ 6095056848372187562659840 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 18285170545116562687979521) ^ 3657034109023312537595904 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 18285170545116562687979521) ^ 64973973502935306240 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 18285170545116562687979521) ^ 56772315317411450880 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (11 : ZMod 18285170545116562687979521) ^ 5568948536340480 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_27632281097561790559530989 : Nat.Prime 27632281097561790559530989 := by
  apply lucas_primality 27632281097561790559530989 (2 : ZMod 27632281097561790559530989)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101, 1), (139, 1), (492062844532405986173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101, 1), (139, 1), (492062844532405986173, 1)] : List FactorBlock).map factorBlockValue).prod) = 27632281097561790559530989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_101
      · exact prime_seventyBP_139
      · exact prime_seventyBP_492062844532405986173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27632281097561790559530989) ^ 13816140548780895279765494 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 27632281097561790559530989) ^ 273586941560017728312188 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 27632281097561790559530989) ^ 198793389191092018413892 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 27632281097561790559530989) ^ 56156 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_28815697035932298999232351 : Nat.Prime 28815697035932298999232351 := by
  apply lucas_primality 28815697035932298999232351 (6 : ZMod 28815697035932298999232351)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (31307, 1), (937369787, 1), (6546142661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (31307, 1), (937369787, 1), (6546142661, 1)] : List FactorBlock).map factorBlockValue).prod) = 28815697035932298999232351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_31307
      · exact prime_seventyBP_937369787
      · exact prime_seventyBP_6546142661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 28815697035932298999232351) ^ 14407848517966149499616175 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 28815697035932298999232351) ^ 9605232345310766333077450 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 28815697035932298999232351) ^ 5763139407186459799846470 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 28815697035932298999232351) ^ 920423452771977481050 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 28815697035932298999232351) ^ 30741013243189050 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (6 : ZMod 28815697035932298999232351) ^ 4401935388241350 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_75855803746285575367365089 : Nat.Prime 75855803746285575367365089 := by
  apply lucas_primality 75855803746285575367365089 (3 : ZMod 75855803746285575367365089)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (103, 1), (1770346427984633480381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (103, 1), (1770346427984633480381, 1)] : List FactorBlock).map factorBlockValue).prod) = 75855803746285575367365089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_13
      · exact prime_seventyBP_103
      · exact prime_seventyBP_1770346427984633480381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 75855803746285575367365089) ^ 37927901873142787683682544 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 75855803746285575367365089) ^ 5835061826637351951335776 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 75855803746285575367365089) ^ 736464114041607527838496 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 75855803746285575367365089) ^ 42848 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_97020729058848256419455231 : Nat.Prime 97020729058848256419455231 := by
  apply lucas_primality 97020729058848256419455231 (7 : ZMod 97020729058848256419455231)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (41, 1), (2069, 1), (2129, 1), (13397, 1), (373211, 1), (826493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (41, 1), (2069, 1), (2129, 1), (13397, 1), (373211, 1), (826493, 1)] : List FactorBlock).map factorBlockValue).prod) = 97020729058848256419455231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_13
      · exact prime_seventyBP_41
      · exact prime_seventyBP_2069
      · exact prime_seventyBP_2129
      · exact prime_seventyBP_13397
      · exact prime_seventyBP_373211
      · exact prime_seventyBP_826493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 97020729058848256419455231) ^ 48510364529424128209727615 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 97020729058848256419455231) ^ 19404145811769651283891046 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 97020729058848256419455231) ^ 7463133004526788955342710 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 97020729058848256419455231) ^ 2366359245337762351694030 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 97020729058848256419455231) ^ 46892570835596064001670 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 97020729058848256419455231) ^ 45571032906927316307870 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 97020729058848256419455231) ^ 7241974252358606883590 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 97020729058848256419455231) ^ 259962136857831779930 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 97020729058848256419455231) ^ 117388446192343137110 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_111085479043218205001067533 : Nat.Prime 111085479043218205001067533 := by
  apply lucas_primality 111085479043218205001067533 (2 : ZMod 111085479043218205001067533)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (957633440027743146560927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (957633440027743146560927, 1)] : List FactorBlock).map factorBlockValue).prod) = 111085479043218205001067533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_29
      · exact prime_seventyBP_957633440027743146560927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 111085479043218205001067533) ^ 55542739521609102500533766 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 111085479043218205001067533) ^ 3830533760110972586243708 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 111085479043218205001067533) ^ 116 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_122787361850441487723731917 : Nat.Prime 122787361850441487723731917 := by
  apply lucas_primality 122787361850441487723731917 (2 : ZMod 122787361850441487723731917)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2927, 1), (8573, 1), (135923835668323961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2927, 1), (8573, 1), (135923835668323961, 1)] : List FactorBlock).map factorBlockValue).prod) = 122787361850441487723731917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_2927
      · exact prime_seventyBP_8573
      · exact prime_seventyBP_135923835668323961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 122787361850441487723731917) ^ 61393680925220743861865958 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 122787361850441487723731917) ^ 40929120616813829241243972 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 122787361850441487723731917) ^ 41949901554643487435508 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 122787361850441487723731917) ^ 14322566412042632418492 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 122787361850441487723731917) ^ 903354156 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_205867367878600902302973413 : Nat.Prime 205867367878600902302973413 := by
  apply lucas_primality 205867367878600902302973413 (2 : ZMod 205867367878600902302973413)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (44657, 1), (1152492150606852801929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (44657, 1), (1152492150606852801929, 1)] : List FactorBlock).map factorBlockValue).prod) = 205867367878600902302973413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_44657
      · exact prime_seventyBP_1152492150606852801929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 205867367878600902302973413) ^ 102933683939300451151486706 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 205867367878600902302973413) ^ 4609968602427411207716 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 205867367878600902302973413) ^ 178628 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_229885227464437674238320311 : Nat.Prime 229885227464437674238320311 := by
  apply lucas_primality 229885227464437674238320311 (7 : ZMod 229885227464437674238320311)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (41, 1), (9109, 1), (5595821083469205409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (41, 1), (9109, 1), (5595821083469205409, 1)] : List FactorBlock).map factorBlockValue).prod) = 229885227464437674238320311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_5
      · exact prime_seventyBP_11
      · exact prime_seventyBP_41
      · exact prime_seventyBP_9109
      · exact prime_seventyBP_5595821083469205409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 229885227464437674238320311) ^ 114942613732218837119160155 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 229885227464437674238320311) ^ 45977045492887534847664062 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 229885227464437674238320311) ^ 20898657042221606748938210 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 229885227464437674238320311) ^ 5606956767425309127763910 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 229885227464437674238320311) ^ 25237153086446116394590 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (7 : ZMod 229885227464437674238320311) ^ 41081590 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_240577563625574310249404977 : Nat.Prime 240577563625574310249404977 := by
  apply lucas_primality 240577563625574310249404977 (5 : ZMod 240577563625574310249404977)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 2), (17, 2), (19, 1), (5503, 1), (18947, 1), (59553204941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 2), (17, 2), (19, 1), (5503, 1), (18947, 1), (59553204941, 1)] : List FactorBlock).map factorBlockValue).prod) = 240577563625574310249404977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_7
      · exact prime_seventyBP_17
      · exact prime_seventyBP_19
      · exact prime_seventyBP_5503
      · exact prime_seventyBP_18947
      · exact prime_seventyBP_59553204941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 240577563625574310249404977) ^ 120288781812787155124702488 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 240577563625574310249404977) ^ 80192521208524770083134992 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 240577563625574310249404977) ^ 34368223375082044321343568 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 240577563625574310249404977) ^ 14151621389739665308788528 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 240577563625574310249404977) ^ 12661977032924963697337104 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 240577563625574310249404977) ^ 43717529279588280982992 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 240577563625574310249404977) ^ 12697396085162522312208 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 240577563625574310249404977) ^ 4039708087313136 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_259431604662061325159232953 : Nat.Prime 259431604662061325159232953 := by
  apply lucas_primality 259431604662061325159232953 (3 : ZMod 259431604662061325159232953)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (3517, 1), (201953, 1), (592951937457647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (3517, 1), (201953, 1), (592951937457647, 1)] : List FactorBlock).map factorBlockValue).prod) = 259431604662061325159232953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_11
      · exact prime_seventyBP_3517
      · exact prime_seventyBP_201953
      · exact prime_seventyBP_592951937457647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 259431604662061325159232953) ^ 129715802331030662579616476 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 259431604662061325159232953) ^ 37061657808865903594176136 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 259431604662061325159232953) ^ 23584691332914665923566632 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 259431604662061325159232953) ^ 73765028337236657708056 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 259431604662061325159232953) ^ 1284613769847743411384 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 259431604662061325159232953) ^ 437525519816 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_361391623961561409282948961 : Nat.Prime 361391623961561409282948961 := by
  apply lucas_primality 361391623961561409282948961 (19 : ZMod 361391623961561409282948961)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (13, 1), (139, 1), (6793, 1), (61336229903205827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (13, 1), (139, 1), (6793, 1), (61336229903205827, 1)] : List FactorBlock).map factorBlockValue).prod) = 361391623961561409282948961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_13
      · exact prime_seventyBP_139
      · exact prime_seventyBP_6793
      · exact prime_seventyBP_61336229903205827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 361391623961561409282948961) ^ 180695811980780704641474480 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (19 : ZMod 361391623961561409282948961) ^ 120463874653853803094316320 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (19 : ZMod 361391623961561409282948961) ^ 72278324792312281856589792 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (19 : ZMod 361391623961561409282948961) ^ 27799355689350877637149920 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (19 : ZMod 361391623961561409282948961) ^ 2599939740730657620740640 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (19 : ZMod 361391623961561409282948961) ^ 53200592368844606106720 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (19 : ZMod 361391623961561409282948961) ^ 5891976480 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_467563174503941032349126057 : Nat.Prime 467563174503941032349126057 := by
  apply lucas_primality 467563174503941032349126057 (3 : ZMod 467563174503941032349126057)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (217879978931, 1), (38320833528721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (217879978931, 1), (38320833528721, 1)] : List FactorBlock).map factorBlockValue).prod) = 467563174503941032349126057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_7
      · exact prime_seventyBP_217879978931
      · exact prime_seventyBP_38320833528721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 467563174503941032349126057) ^ 233781587251970516174563028 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 467563174503941032349126057) ^ 66794739214848718907018008 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 467563174503941032349126057) ^ 2145966677608376 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (3 : ZMod 467563174503941032349126057) ^ 12201278820136 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1235204207271605413817840479 : Nat.Prime 1235204207271605413817840479 := by
  apply lucas_primality 1235204207271605413817840479 (15 : ZMod 1235204207271605413817840479)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (205867367878600902302973413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (205867367878600902302973413, 1)] : List FactorBlock).map factorBlockValue).prod) = 1235204207271605413817840479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_205867367878600902302973413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (15 : ZMod 1235204207271605413817840479) ^ 617602103635802706908920239 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (15 : ZMod 1235204207271605413817840479) ^ 411734735757201804605946826 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (15 : ZMod 1235204207271605413817840479) ^ 6 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_1379311364786626045429921867 : Nat.Prime 1379311364786626045429921867 := by
  apply lucas_primality 1379311364786626045429921867 (5 : ZMod 1379311364786626045429921867)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (229885227464437674238320311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (229885227464437674238320311, 1)] : List FactorBlock).map factorBlockValue).prod) = 1379311364786626045429921867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_229885227464437674238320311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1379311364786626045429921867) ^ 689655682393313022714960933 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1379311364786626045429921867) ^ 459770454928875348476640622 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1379311364786626045429921867) ^ 6 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_4597704549288753484766406223 : Nat.Prime 4597704549288753484766406223 := by
  apply lucas_primality 4597704549288753484766406223 (5 : ZMod 4597704549288753484766406223)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (37, 1), (3671, 1), (557583919, 1), (10107863849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (37, 1), (3671, 1), (557583919, 1), (10107863849, 1)] : List FactorBlock).map factorBlockValue).prod) = 4597704549288753484766406223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_7
      · exact prime_seventyBP_11
      · exact prime_seventyBP_13
      · exact prime_seventyBP_37
      · exact prime_seventyBP_3671
      · exact prime_seventyBP_557583919
      · exact prime_seventyBP_10107863849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4597704549288753484766406223) ^ 2298852274644376742383203111 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4597704549288753484766406223) ^ 1532568183096251161588802074 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4597704549288753484766406223) ^ 656814935612679069252343746 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4597704549288753484766406223) ^ 417973140844432134978764202 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4597704549288753484766406223) ^ 353669580714519498828185094 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4597704549288753484766406223) ^ 124262285115912256345038006 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4597704549288753484766406223) ^ 1252439267035890352701282 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4597704549288753484766406223) ^ 8245762463046846738 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4597704549288753484766406223) ^ 454864115501874078 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_13793113647866260454299218683 : Nat.Prime 13793113647866260454299218683 := by
  apply lucas_primality 13793113647866260454299218683 (2 : ZMod 13793113647866260454299218683)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (311, 1), (1559, 1), (4001, 1), (86710842632149349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (311, 1), (1559, 1), (4001, 1), (86710842632149349, 1)] : List FactorBlock).map factorBlockValue).prod) = 13793113647866260454299218683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_41
      · exact prime_seventyBP_311
      · exact prime_seventyBP_1559
      · exact prime_seventyBP_4001
      · exact prime_seventyBP_86710842632149349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13793113647866260454299218683) ^ 6896556823933130227149609341 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13793113647866260454299218683) ^ 336417406045518547665834602 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13793113647866260454299218683) ^ 44350847742335242618325462 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13793113647866260454299218683) ^ 8847410935129095865490198 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13793113647866260454299218683) ^ 3447416557827108336490682 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13793113647866260454299218683) ^ 159070229618 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_27586227295732520908598437357 : Nat.Prime 27586227295732520908598437357 := by
  apply lucas_primality 27586227295732520908598437357 (5 : ZMod 27586227295732520908598437357)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (281, 1), (11357393, 1), (720321023399680961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (281, 1), (11357393, 1), (720321023399680961, 1)] : List FactorBlock).map factorBlockValue).prod) = 27586227295732520908598437357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_281
      · exact prime_seventyBP_11357393
      · exact prime_seventyBP_720321023399680961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 27586227295732520908598437357) ^ 13793113647866260454299218678 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 27586227295732520908598437357) ^ 9195409098577506969532812452 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 27586227295732520908598437357) ^ 98171627386948472984336076 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 27586227295732520908598437357) ^ 2428922490903724200492 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (5 : ZMod 27586227295732520908598437357) ^ 38297129196 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_82758681887197562725795312021 : Nat.Prime 82758681887197562725795312021 := by
  apply lucas_primality 82758681887197562725795312021 (2 : ZMod 82758681887197562725795312021)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1379311364786626045429921867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1379311364786626045429921867, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_3
      · exact prime_seventyBP_5
      · exact prime_seventyBP_1379311364786626045429921867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 82758681887197562725795312021) ^ 41379340943598781362897656010 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 82758681887197562725795312021) ^ 27586227295732520908598437340 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 82758681887197562725795312021) ^ 16551736377439512545159062404 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 82758681887197562725795312021) ^ 60 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem prime_seventyBP_82758681887197562725795312037 : Nat.Prime 82758681887197562725795312037 := by
  apply lucas_primality 82758681887197562725795312037 (2 : ZMod 82758681887197562725795312037)
  · rw [← seventyBPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (229171, 1), (3113120389668276719951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (229171, 1), (3113120389668276719951, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyBP_2
      · exact prime_seventyBP_29
      · exact prime_seventyBP_229171
      · exact prime_seventyBP_3113120389668276719951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 82758681887197562725795312037) ^ 41379340943598781362897656018 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 82758681887197562725795312037) ^ 2853747651282674576751562484 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 82758681887197562725795312037) ^ 361121965201520099514316 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide
    · change (2 : ZMod 82758681887197562725795312037) ^ 26583836 ≠ 1
      rw [← seventyBPFastPow_eq_pow]
      decide

private theorem phi_seventyBP_82758681887197562725795312000 : Nat.totient 82758681887197562725795312000 = 33103472754879025090318118400 := by
  rw [← show ((([(2, 7), (5, 3), (5172417617949847670362207, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_5, prime_seventyBP_5172417617949847670362207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312001 : Nat.totient 82758681887197562725795312001 = 81752235490805143453397342400 := by
  rw [← show ((([(83, 1), (8741, 1), (2001730781, 1), (56986067069707, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_83, prime_seventyBP_8741, prime_seventyBP_2001730781, prime_seventyBP_56986067069707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312002 : Nat.totient 82758681887197562725795312002 = 26915930789750486757807416064 := by
  rw [← show ((([(2, 1), (3, 1), (43, 1), (937, 1), (342337337069476072926937, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_3, prime_seventyBP_43, prime_seventyBP_937, prime_seventyBP_342337337069476072926937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312003 : Nat.totient 82758681887197562725795312003 = 70936013043374442686347319304 := by
  rw [← show ((([(7, 1), (25380549683, 1), (465816106770417863, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_7, prime_seventyBP_25380549683, prime_seventyBP_465816106770417863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312004 : Nat.totient 82758681887197562725795312004 = 41379340943527752378809729064 := by
  rw [← show ((([(2, 2), (582579355067, 1), (35513909464608403, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_582579355067, prime_seventyBP_35513909464608403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312005 : Nat.totient 82758681887197562725795312005 = 44137775433665244024292394880 := by
  rw [← show ((([(3, 2), (5, 1), (234571, 1), (589439437, 1), (13301099508407, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_3, prime_seventyBP_5, prime_seventyBP_234571, prime_seventyBP_589439437, prime_seventyBP_13301099508407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312006 : Nat.totient 82758681887197562725795312006 = 41379339784562072629174504440 := by
  rw [← show ((([(2, 1), (35701493, 1), (1159036708733687450071, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_35701493, prime_seventyBP_1159036708733687450071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312007 : Nat.totient 82758681887197562725795312007 = 72640849305377171044585226560 := by
  rw [← show ((([(11, 1), (29, 1), (259431604662061325159232953, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_11, prime_seventyBP_29, prime_seventyBP_259431604662061325159232953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312008 : Nat.totient 82758681887197562725795312008 = 27496575188785432685187219456 := by
  rw [← show ((([(2, 3), (3, 1), (373, 1), (1753, 1), (55178143847, 1), (95575039969, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_3, prime_seventyBP_373, prime_seventyBP_1753, prime_seventyBP_55178143847, prime_seventyBP_95575039969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312009 : Nat.totient 82758681887197562725795312009 = 76392629420258688332573609040 := by
  rw [← show ((([(13, 1), (5426567411, 1), (1173126945766296863, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_13, prime_seventyBP_5426567411, prime_seventyBP_1173126945766296863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312010 : Nat.totient 82758681887197562725795312010 = 26225380946465686482702036480 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (19, 1), (41, 1), (1517672508476023523304517, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_5, prime_seventyBP_7, prime_seventyBP_19, prime_seventyBP_41, prime_seventyBP_1517672508476023523304517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312011 : Nat.totient 82758681887197562725795312011 = 54395203398042119156175480800 := by
  rw [← show ((([(3, 1), (71, 1), (311957, 1), (1245487078719025374371, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_3, prime_seventyBP_71, prime_seventyBP_311957, prime_seventyBP_1245487078719025374371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312012 : Nat.totient 82758681887197562725795312012 = 40640851359838906342941265920 := by
  rw [← show ((([(2, 2), (61, 1), (677, 1), (2042767, 1), (248186929, 1), (988182893, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_61, prime_seventyBP_677, prime_seventyBP_2042767, prime_seventyBP_248186929, prime_seventyBP_988182893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312013 : Nat.totient 82758681887197562725795312013 = 80254759245675871876195800240 := by
  rw [← show ((([(47, 1), (109, 1), (16154339622720586126448431, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_47, prime_seventyBP_109, prime_seventyBP_16154339622720586126448431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312014 : Nat.totient 82758681887197562725795312014 = 27586227295732520908598437332 := by
  rw [← show ((([(2, 1), (3, 2), (4597704549288753484766406223, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_3, prime_seventyBP_4597704549288753484766406223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312015 : Nat.totient 82758681887197562725795312015 = 64070732037769466783783961600 := by
  rw [← show ((([(5, 1), (31, 1), (126739, 1), (4164800047, 1), (1011526896161, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_5, prime_seventyBP_31, prime_seventyBP_126739, prime_seventyBP_4164800047, prime_seventyBP_1011526896161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312016 : Nat.totient 82758681887197562725795312016 = 38945262064465212963731564544 := by
  rw [← show ((([(2, 4), (17, 1), (396206952469, 1), (767931652848037, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_17, prime_seventyBP_396206952469, prime_seventyBP_767931652848037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312017 : Nat.totient 82758681887197562725795312017 = 45208502442792603156241612800 := by
  rw [← show ((([(3, 1), (7, 1), (23, 1), (1741, 1), (630997, 1), (15021131, 1), (10383355777, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_3, prime_seventyBP_7, prime_seventyBP_23, prime_seventyBP_1741, prime_seventyBP_630997, prime_seventyBP_15021131, prime_seventyBP_10383355777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312018 : Nat.totient 82758681887197562725795312018 = 37601134235825740030839918960 := by
  rw [← show ((([(2, 1), (11, 1), (2287, 1), (1644844017315211724883637, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_11, prime_seventyBP_2287, prime_seventyBP_1644844017315211724883637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312019 : Nat.totient 82758681887197562725795312019 = 82758681887194047211636658400 := by
  rw [← show ((([(23700774578801, 1), (3491813384074819, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_23700774578801, prime_seventyBP_3491813384074819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312020 : Nat.totient 82758681887197562725795312020 = 22068981836586016726878749856 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (1379311364786626045429921867, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_3, prime_seventyBP_5, prime_seventyBP_1379311364786626045429921867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312021 : Nat.totient 82758681887197562725795312021 = 82758681887197562725795312020 := by
  rw [← show ((([(82758681887197562725795312021, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_82758681887197562725795312021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312022 : Nat.totient 82758681887197562725795312022 = 37973446532860611687462890496 := by
  rw [← show ((([(2, 1), (13, 1), (239, 1), (607, 1), (101107, 1), (3088873, 1), (70254208949, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_13, prime_seventyBP_239, prime_seventyBP_607, prime_seventyBP_101107, prime_seventyBP_3088873, prime_seventyBP_70254208949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312023 : Nat.totient 82758681887197562725795312023 = 55088459421893779590694056960 := by
  rw [← show ((([(3, 4), (659, 1), (201281, 1), (7702653292189832477, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_3, prime_seventyBP_659, prime_seventyBP_201281, prime_seventyBP_7702653292189832477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312024 : Nat.totient 82758681887197562725795312024 = 35136516088687337106835153920 := by
  rw [← show ((([(2, 3), (7, 1), (107, 1), (2557631, 1), (5400125749137691937, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_7, prime_seventyBP_107, prime_seventyBP_2557631, prime_seventyBP_5400125749137691937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312025 : Nat.totient 82758681887197562725795312025 = 66202728227341194479343724800 := by
  rw [← show ((([(5, 2), (15733, 1), (13711771, 1), (15654523, 1), (980231429, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_5, prime_seventyBP_15733, prime_seventyBP_13711771, prime_seventyBP_15654523, prime_seventyBP_980231429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312026 : Nat.totient 82758681887197562725795312026 = 27174492559975319103992490384 := by
  rw [← show ((([(2, 1), (3, 1), (67, 1), (205867367878600902302973413, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_3, prime_seventyBP_67, prime_seventyBP_205867367878600902302973413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312027 : Nat.totient 82758681887197562725795312027 = 82756698320529411433258526208 := by
  rw [← show ((([(44273, 1), (724123, 1), (2581441404682826513, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_44273, prime_seventyBP_724123, prime_seventyBP_2581441404682826513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312028 : Nat.totient 82758681887197562725795312028 = 41344480504724645911033375920 := by
  rw [← show ((([(2, 2), (1187, 1), (17430219437067725932138861, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_1187, prime_seventyBP_17430219437067725932138861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312029 : Nat.totient 82758681887197562725795312029 = 47497749694089378666812928000 := by
  rw [← show ((([(3, 1), (11, 1), (19, 1), (4177, 1), (6151, 1), (921203, 1), (1378253, 1), (4046239, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_3, prime_seventyBP_11, prime_seventyBP_19, prime_seventyBP_4177, prime_seventyBP_6151, prime_seventyBP_921203, prime_seventyBP_1378253, prime_seventyBP_4046239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312030 : Nat.totient 82758681887197562725795312030 = 32542301715489840139239377920 := by
  rw [← show ((([(2, 1), (5, 1), (59, 1), (342413, 1), (169905161, 1), (2411041787669, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_5, prime_seventyBP_59, prime_seventyBP_342413, prime_seventyBP_169905161, prime_seventyBP_2411041787669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312031 : Nat.totient 82758681887197562725795312031 = 70887790059734146182530306040 := by
  rw [← show ((([(7, 1), (1471, 1), (8037164405865549453801623, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_7, prime_seventyBP_1471, prime_seventyBP_8037164405865549453801623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312032 : Nat.totient 82758681887197562725795312032 = 27447171397838702753296711680 := by
  rw [← show ((([(2, 5), (3, 2), (199, 1), (64817, 1), (3356593, 1), (6637131006931, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_3, prime_seventyBP_199, prime_seventyBP_64817, prime_seventyBP_3356593, prime_seventyBP_6637131006931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312033 : Nat.totient 82758681887197562725795312033 = 75689349660134782501253216256 := by
  rw [← show ((([(17, 2), (37, 1), (827, 1), (17257, 1), (542304476636213279, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_17, prime_seventyBP_37, prime_seventyBP_827, prime_seventyBP_17257, prime_seventyBP_542304476636213279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312034 : Nat.totient 82758681887197562725795312034 = 41075192076131295485619921024 := by
  rw [← show ((([(2, 1), (137, 1), (19469, 1), (15513841747895224548589, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_137, prime_seventyBP_19469, prime_seventyBP_15513841747895224548589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312035 : Nat.totient 82758681887197562725795312035 = 40716332210782592851863674880 := by
  rw [← show ((([(3, 1), (5, 1), (13, 1), (1621, 1), (32083, 1), (1696574303, 1), (4810033297, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_3, prime_seventyBP_5, prime_seventyBP_13, prime_seventyBP_1621, prime_seventyBP_32083, prime_seventyBP_1696574303, prime_seventyBP_4810033297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312036 : Nat.totient 82758681887197562725795312036 = 39952292783215622651012724000 := by
  rw [← show ((([(2, 2), (29, 1), (229171, 1), (3113120389668276719951, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_29, prime_seventyBP_229171, prime_seventyBP_3113120389668276719951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312037 : Nat.totient 82758681887197562725795312037 = 82758681887197562725795312036 := by
  rw [← show ((([(82758681887197562725795312037, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_82758681887197562725795312037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312038 : Nat.totient 82758681887197562725795312038 = 23391555114373029039957000192 := by
  rw [← show ((([(2, 1), (3, 1), (7, 2), (103, 1), (1277, 1), (4139, 1), (103177, 1), (5011408325089, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_3, prime_seventyBP_7, prime_seventyBP_103, prime_seventyBP_1277, prime_seventyBP_4139, prime_seventyBP_103177, prime_seventyBP_5011408325089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312039 : Nat.totient 82758681887197562725795312039 = 82565947419404054439220986816 := by
  rw [← show ((([(569, 1), (1747, 1), (83254629716418266338373, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_569, prime_seventyBP_1747, prime_seventyBP_83254629716418266338373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312040 : Nat.totient 82758681887197562725795312040 = 28785628482503500078537496320 := by
  rw [← show ((([(2, 3), (5, 1), (11, 1), (23, 1), (8177735364347585249584517, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_5, prime_seventyBP_11, prime_seventyBP_23, prime_seventyBP_8177735364347585249584517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312041 : Nat.totient 82758681887197562725795312041 = 54401893309443431568319977600 := by
  rw [← show ((([(3, 2), (127, 1), (223, 1), (631, 1), (12619, 1), (40776333437372021, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_3, prime_seventyBP_127, prime_seventyBP_223, prime_seventyBP_631, prime_seventyBP_12619, prime_seventyBP_40776333437372021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312042 : Nat.totient 82758681887197562725795312042 = 40238530891974244135157289984 := by
  rw [← show ((([(2, 1), (53, 1), (113, 1), (51059, 1), (989548687, 1), (136747622533, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_53, prime_seventyBP_113, prime_seventyBP_51059, prime_seventyBP_989548687, prime_seventyBP_136747622533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312043 : Nat.totient 82758681887197562725795312043 = 82661661158138714469375855960 := by
  rw [← show ((([(853, 1), (97020729058848256419455231, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_853, prime_seventyBP_97020729058848256419455231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312044 : Nat.totient 82758681887197562725795312044 = 27586227258284930900637019600 := by
  rw [← show ((([(2, 2), (3, 1), (736662287, 1), (9361897501253692151, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_3, prime_seventyBP_736662287, prime_seventyBP_9361897501253692151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312045 : Nat.totient 82758681887197562725795312045 = 55429007978673570200142758400 := by
  rw [← show ((([(5, 1), (7, 1), (43, 1), (884309, 1), (62183193205238520601, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_5, prime_seventyBP_7, prime_seventyBP_43, prime_seventyBP_884309, prime_seventyBP_62183193205238520601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312046 : Nat.totient 82758681887197562725795312046 = 39495968377451775406035763200 := by
  rw [← show ((([(2, 1), (31, 1), (73, 1), (18285170545116562687979521, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_31, prime_seventyBP_73, prime_seventyBP_18285170545116562687979521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312047 : Nat.totient 82758681887197562725795312047 = 55063161884935967770879303680 := by
  rw [← show ((([(3, 1), (563, 1), (5527, 1), (41453, 1), (22332481, 1), (9576383093, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_3, prime_seventyBP_563, prime_seventyBP_5527, prime_seventyBP_41453, prime_seventyBP_22332481, prime_seventyBP_9576383093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312048 : Nat.totient 82758681887197562725795312048 = 36168553666067457405456580608 := by
  rw [← show ((([(2, 4), (13, 1), (19, 1), (2083, 1), (661093, 1), (19129889, 1), (794936339, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_13, prime_seventyBP_19, prime_seventyBP_2083, prime_seventyBP_661093, prime_seventyBP_19129889, prime_seventyBP_794936339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312049 : Nat.totient 82758681887197562725795312049 = 81406618754241383729013251520 := by
  rw [← show ((([(79, 1), (269, 1), (112111, 1), (34736492790707656309, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_79, prime_seventyBP_269, prime_seventyBP_112111, prime_seventyBP_34736492790707656309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312050 : Nat.totient 82758681887197562725795312050 = 20770806406833954218121984000 := by
  rw [← show ((([(2, 1), (3, 3), (5, 2), (17, 1), (752567099, 1), (4791656170655801, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_3, prime_seventyBP_5, prime_seventyBP_17, prime_seventyBP_752567099, prime_seventyBP_4791656170655801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312051 : Nat.totient 82758681887197562725795312051 = 73391230772566574337947769600 := by
  rw [← show ((([(11, 2), (41, 1), (8219, 1), (2029669649012328102889, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_11, prime_seventyBP_41, prime_seventyBP_8219, prime_seventyBP_2029669649012328102889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312052 : Nat.totient 82758681887197562725795312052 = 35468006522933765028946887360 := by
  rw [← show ((([(2, 2), (7, 1), (235040173961, 1), (12575157516465619, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_7, prime_seventyBP_235040173961, prime_seventyBP_12575157516465619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312053 : Nat.totient 82758681887197562725795312053 = 55172454350501643605240911200 := by
  rw [← show ((([(3, 1), (228966121, 1), (120481699105749015631, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_3, prime_seventyBP_228966121, prime_seventyBP_120481699105749015631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312054 : Nat.totient 82758681887197562725795312054 = 41379255767461811402725656840 := by
  rw [← show ((([(2, 1), (485923, 1), (2072350739, 1), (41091581196691, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_485923, prime_seventyBP_2072350739, prime_seventyBP_41091581196691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312055 : Nat.totient 82758681887197562725795312055 = 66096416385367803018398123296 := by
  rw [← show ((([(5, 1), (599, 1), (27632281097561790559530989, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_5, prime_seventyBP_599, prime_seventyBP_27632281097561790559530989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312056 : Nat.totient 82758681887197562725795312056 = 27580978794252241735872675840 := by
  rw [← show ((([(2, 3), (3, 1), (5281, 1), (1728253, 1), (3110369, 1), (121469409857, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_3, prime_seventyBP_5281, prime_seventyBP_1728253, prime_seventyBP_3110369, prime_seventyBP_121469409857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312057 : Nat.totient 82758681887197562725795312057 = 82631229423107034369369609072 := by
  rw [← show ((([(1063, 1), (1667, 1), (46702991605177118513717, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_1063, prime_seventyBP_1667, prime_seventyBP_46702991605177118513717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312058 : Nat.totient 82758681887197562725795312058 = 41256553581748339875173923776 := by
  rw [← show ((([(2, 1), (337, 1), (122787361850441487723731917, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_337, prime_seventyBP_122787361850441487723731917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312059 : Nat.totient 82758681887197562725795312059 = 47066546358218439266459414400 := by
  rw [← show ((([(3, 2), (7, 1), (211, 1), (18226121, 1), (341583049231925903, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_3, prime_seventyBP_7, prime_seventyBP_211, prime_seventyBP_18226121, prime_seventyBP_341583049231925903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312060 : Nat.totient 82758681887197562725795312060 = 32337098029398171101179127040 := by
  rw [← show ((([(2, 2), (5, 1), (47, 1), (523, 1), (339067, 1), (21613019, 1), (22971167231, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_5, prime_seventyBP_47, prime_seventyBP_523, prime_seventyBP_339067, prime_seventyBP_21613019, prime_seventyBP_22971167231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312061 : Nat.totient 82758681887197562725795312061 = 75971961294559155903060244800 := by
  rw [← show ((([(13, 1), (197, 1), (2311, 1), (13983118593839111947291, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_13, prime_seventyBP_197, prime_seventyBP_2311, prime_seventyBP_13983118593839111947291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312062 : Nat.totient 82758681887197562725795312062 = 24960889917813741632632953600 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (233, 1), (2531, 1), (2126285429826030873709, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_3, prime_seventyBP_11, prime_seventyBP_233, prime_seventyBP_2531, prime_seventyBP_2126285429826030873709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312063 : Nat.totient 82758681887197562725795312063 = 78908462563048996553374445824 := by
  rw [← show ((([(23, 1), (353, 1), (2843, 1), (3585371515658396110139, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_23, prime_seventyBP_353, prime_seventyBP_2843, prime_seventyBP_3585371515658396110139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312064 : Nat.totient 82758681887197562725795312064 = 41244554622293253716785678080 := by
  rw [← show ((([(2, 6), (307, 1), (212105071, 1), (19858395861400883, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_307, prime_seventyBP_212105071, prime_seventyBP_19858395861400883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312065 : Nat.totient 82758681887197562725795312065 = 42615948735274103010776236800 := by
  rw [← show ((([(3, 1), (5, 1), (29, 1), (2632151, 1), (72279228440482697149, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_3, prime_seventyBP_5, prime_seventyBP_29, prime_seventyBP_2632151, prime_seventyBP_72279228440482697149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312066 : Nat.totient 82758681887197562725795312066 = 35468006523083431590767238864 := by
  rw [← show ((([(2, 1), (7, 1), (34370740734973, 1), (171987402485603, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_7, prime_seventyBP_34370740734973, prime_seventyBP_171987402485603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312067 : Nat.totient 82758681887197562725795312067 = 73735414576158340260774305280 := by
  rw [← show ((([(17, 1), (19, 1), (1327, 1), (83722757, 1), (2306198038899011, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_17, prime_seventyBP_19, prime_seventyBP_1327, prime_seventyBP_83722757, prime_seventyBP_2306198038899011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312068 : Nat.totient 82758681887197562725795312068 = 27488053248066933774525235200 := by
  rw [← show ((([(2, 2), (3, 2), (281, 1), (11357393, 1), (720321023399680961, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_3, prime_seventyBP_281, prime_seventyBP_11357393, prime_seventyBP_720321023399680961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312069 : Nat.totient 82758681887197562725795312069 = 82397290263236001316512362880 := by
  rw [← show ((([(229, 1), (361391623961561409282948961, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_229, prime_seventyBP_361391623961561409282948961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312070 : Nat.totient 82758681887197562725795312070 = 32030835217502774762619273600 := by
  rw [← show ((([(2, 1), (5, 1), (37, 1), (181, 1), (1235757531539458902878831, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_5, prime_seventyBP_37, prime_seventyBP_181, prime_seventyBP_1235757531539458902878831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312071 : Nat.totient 82758681887197562725795312071 = 55172454591465041817196874712 := by
  rw [← show ((([(3, 1), (27586227295732520908598437357, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_3, prime_seventyBP_27586227295732520908598437357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312072 : Nat.totient 82758681887197562725795312072 = 41264078155455052166900725200 := by
  rw [← show ((([(2, 3), (359, 1), (28815697035932298999232351, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_359, prime_seventyBP_28815697035932298999232351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312073 : Nat.totient 82758681887197562725795312073 = 63101462536919669104266854400 := by
  rw [← show ((([(7, 1), (11, 1), (61, 1), (193, 1), (91292625198089799051313, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_7, prime_seventyBP_11, prime_seventyBP_61, prime_seventyBP_193, prime_seventyBP_91292625198089799051313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312074 : Nat.totient 82758681887197562725795312074 = 25463794943008129841369302272 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (61379, 1), (17286184886419760772977, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_3, prime_seventyBP_13, prime_seventyBP_61379, prime_seventyBP_17286184886419760772977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312075 : Nat.totient 82758681887197562725795312075 = 65460459875647906141325088000 := by
  rw [← show ((([(5, 2), (89, 1), (25301, 1), (1470096565658639645647, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_5, prime_seventyBP_89, prime_seventyBP_25301, prime_seventyBP_1470096565658639645647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312076 : Nat.totient 82758681887197562725795312076 = 41379340943583504921496264992 := by
  rw [← show ((([(2, 2), (2709664143337, 1), (7635511036552187, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_2709664143337, prime_seventyBP_7635511036552187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312077 : Nat.totient 82758681887197562725795312077 = 53392680823819315499928416880 := by
  rw [← show ((([(3, 3), (31, 1), (3110027, 1), (31792446384346837723, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_3, prime_seventyBP_31, prime_seventyBP_3110027, prime_seventyBP_31792446384346837723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312078 : Nat.totient 82758681887197562725795312078 = 41108221497097088868208510656 := by
  rw [← show ((([(2, 1), (163, 1), (2383, 1), (68594249, 1), (1553045633639659, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_163, prime_seventyBP_2383, prime_seventyBP_68594249, prime_seventyBP_1553045633639659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312079 : Nat.totient 82758681887197562725795312079 = 82624984468974540031197087000 := by
  rw [← show ((([(619, 1), (2558157491, 1), (52263156742600351, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_619, prime_seventyBP_2558157491, prime_seventyBP_52263156742600351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312080 : Nat.totient 82758681887197562725795312080 = 18909060413292766537098854400 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (7, 1), (2897, 1), (27893, 1), (8646221, 1), (70507323541, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_3, prime_seventyBP_5, prime_seventyBP_7, prime_seventyBP_2897, prime_seventyBP_27893, prime_seventyBP_8646221, prime_seventyBP_70507323541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312081 : Nat.totient 82758681887197562725795312081 = 82399307111149015742774475456 := by
  rw [← show ((([(397, 1), (547, 1), (597010187, 1), (638342838067157, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_397, prime_seventyBP_547, prime_seventyBP_597010187, prime_seventyBP_638342838067157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312082 : Nat.totient 82758681887197562725795312082 = 40633997335057923473530000000 := by
  rw [← show ((([(2, 1), (71, 1), (251, 1), (148846574021, 1), (15599571035801, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_71, prime_seventyBP_251, prime_seventyBP_148846574021, prime_seventyBP_15599571035801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312083 : Nat.totient 82758681887197562725795312083 = 55165606475075016779657955744 := by
  rw [← show ((([(3, 1), (8059, 1), (26919103, 1), (127160014938533693, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_3, prime_seventyBP_8059, prime_seventyBP_26919103, prime_seventyBP_127160014938533693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312084 : Nat.totient 82758681887197562725795312084 = 34978220036081181076040000000 := by
  rw [← show ((([(2, 2), (11, 1), (17, 1), (83, 1), (1333011434301874278812501, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_11, prime_seventyBP_17, prime_seventyBP_83, prime_seventyBP_1333011434301874278812501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312085 : Nat.totient 82758681887197562725795312085 = 65762603593585177360631978944 := by
  rw [← show ((([(5, 1), (149, 1), (111085479043218205001067533, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_5, prime_seventyBP_149, prime_seventyBP_111085479043218205001067533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312086 : Nat.totient 82758681887197562725795312086 = 24949165565116270378623191040 := by
  rw [← show ((([(2, 1), (3, 2), (19, 1), (23, 1), (521, 1), (27743, 1), (727894566812668657, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_3, prime_seventyBP_19, prime_seventyBP_23, prime_seventyBP_521, prime_seventyBP_27743, prime_seventyBP_727894566812668657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312087 : Nat.totient 82758681887197562725795312087 = 65479320073823236584147510912 := by
  rw [← show ((([(7, 2), (13, 2), (854999, 1), (11688672043745706473, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_7, prime_seventyBP_13, prime_seventyBP_854999, prime_seventyBP_11688672043745706473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312088 : Nat.totient 82758681887197562725795312088 = 40417030689096484121900035968 := by
  rw [← show ((([(2, 3), (43, 1), (240577563625574310249404977, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_43, prime_seventyBP_240577563625574310249404977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312089 : Nat.totient 82758681887197562725795312089 = 54237328242457159752498622496 := by
  rw [← show ((([(3, 1), (59, 1), (467563174503941032349126057, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_3, prime_seventyBP_59, prime_seventyBP_467563174503941032349126057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312090 : Nat.totient 82758681887197562725795312090 = 32744819849079771062179200000 := by
  rw [← show ((([(2, 1), (5, 1), (101, 1), (1061, 1), (8887871, 1), (73733381, 1), (117846019, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_5, prime_seventyBP_101, prime_seventyBP_1061, prime_seventyBP_8887871, prime_seventyBP_73733381, prime_seventyBP_117846019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312091 : Nat.totient 82758681887197562725795312091 = 82758613755504470433242414712 := by
  rw [← show ((([(1214687, 1), (68131693092292551682693, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_1214687, prime_seventyBP_68131693092292551682693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312092 : Nat.totient 82758681887197562725795312092 = 26802945775664314942105600000 := by
  rw [← show ((([(2, 2), (3, 1), (41, 1), (311, 1), (1559, 1), (4001, 1), (86710842632149349, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_3, prime_seventyBP_41, prime_seventyBP_311, prime_seventyBP_1559, prime_seventyBP_4001, prime_seventyBP_86710842632149349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312093 : Nat.totient 82758681887197562725795312093 = 81523477679925957311977471548 := by
  rw [← show ((([(67, 1), (1235204207271605413817840479, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_67, prime_seventyBP_1235204207271605413817840479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312094 : Nat.totient 82758681887197562725795312094 = 33890043678219609565437591552 := by
  rw [← show ((([(2, 1), (7, 1), (29, 1), (97, 1), (17959, 1), (6721328609, 1), (17409188107, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_7, prime_seventyBP_29, prime_seventyBP_97, prime_seventyBP_17959, prime_seventyBP_6721328609, prime_seventyBP_17409188107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312095 : Nat.totient 82758681887197562725795312095 = 39368338095963028784092231680 := by
  rw [← show ((([(3, 2), (5, 1), (11, 1), (53, 1), (226428570409, 1), (13931608828453, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_3, prime_seventyBP_5, prime_seventyBP_11, prime_seventyBP_53, prime_seventyBP_226428570409, prime_seventyBP_13931608828453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312096 : Nat.totient 82758681887197562725795312096 = 41178931382870949190985902080 := by
  rw [← show ((([(2, 5), (389, 1), (439, 1), (2174077, 1), (49746491, 1), (140027099, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_389, prime_seventyBP_439, prime_seventyBP_2174077, prime_seventyBP_49746491, prime_seventyBP_140027099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312097 : Nat.totient 82758681887197562725795312097 = 82579161969780525721319155600 := by
  rw [← show ((([(461, 1), (909356595311, 1), (197414213798507, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_461, prime_seventyBP_909356595311, prime_seventyBP_197414213798507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312098 : Nat.totient 82758681887197562725795312098 = 27586227295732520908598437364 := by
  rw [← show ((([(2, 1), (3, 1), (13793113647866260454299218683, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_3, prime_seventyBP_13793113647866260454299218683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312099 : Nat.totient 82758681887197562725795312099 = 82682826083451277150427945920 := by
  rw [← show ((([(1091, 1), (75855803746285575367365089, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_1091, prime_seventyBP_75855803746285575367365089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312100 : Nat.totient 82758681887197562725795312100 = 30556934420102242536640389120 := by
  rw [← show ((([(2, 2), (5, 2), (13, 1), (260677, 1), (232003769, 1), (1052622037609, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_2, prime_seventyBP_5, prime_seventyBP_13, prime_seventyBP_260677, prime_seventyBP_232003769, prime_seventyBP_1052622037609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyBP_82758681887197562725795312101 : Nat.totient 82758681887197562725795312101 = 44508870930868424484021396480 := by
  rw [← show ((([(3, 1), (7, 1), (17, 1), (727060585421, 1), (318841429100933, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197562725795312101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyBP_3, prime_seventyBP_7, prime_seventyBP_17, prime_seventyBP_727060585421, prime_seventyBP_318841429100933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SeventyBP : certifiedKill 1 82758681887197562725795311999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_seventyBP_82758681887197562725795312000, phi_seventyBP_82758681887197562725795312001, phi_seventyBP_82758681887197562725795312002,
    phi_seventyBP_82758681887197562725795312003, phi_seventyBP_82758681887197562725795312004, phi_seventyBP_82758681887197562725795312005,
    phi_seventyBP_82758681887197562725795312006, phi_seventyBP_82758681887197562725795312007, phi_seventyBP_82758681887197562725795312008,
    phi_seventyBP_82758681887197562725795312009, phi_seventyBP_82758681887197562725795312010, phi_seventyBP_82758681887197562725795312011,
    phi_seventyBP_82758681887197562725795312012, phi_seventyBP_82758681887197562725795312013, phi_seventyBP_82758681887197562725795312014,
    phi_seventyBP_82758681887197562725795312015, phi_seventyBP_82758681887197562725795312016, phi_seventyBP_82758681887197562725795312017,
    phi_seventyBP_82758681887197562725795312018, phi_seventyBP_82758681887197562725795312019, phi_seventyBP_82758681887197562725795312020,
    phi_seventyBP_82758681887197562725795312021, phi_seventyBP_82758681887197562725795312022, phi_seventyBP_82758681887197562725795312023,
    phi_seventyBP_82758681887197562725795312024, phi_seventyBP_82758681887197562725795312025, phi_seventyBP_82758681887197562725795312026,
    phi_seventyBP_82758681887197562725795312027, phi_seventyBP_82758681887197562725795312028, phi_seventyBP_82758681887197562725795312029,
    phi_seventyBP_82758681887197562725795312030, phi_seventyBP_82758681887197562725795312031, phi_seventyBP_82758681887197562725795312032,
    phi_seventyBP_82758681887197562725795312033, phi_seventyBP_82758681887197562725795312034, phi_seventyBP_82758681887197562725795312035,
    phi_seventyBP_82758681887197562725795312036, phi_seventyBP_82758681887197562725795312037, phi_seventyBP_82758681887197562725795312038,
    phi_seventyBP_82758681887197562725795312039, phi_seventyBP_82758681887197562725795312040, phi_seventyBP_82758681887197562725795312041,
    phi_seventyBP_82758681887197562725795312042, phi_seventyBP_82758681887197562725795312043, phi_seventyBP_82758681887197562725795312044,
    phi_seventyBP_82758681887197562725795312045, phi_seventyBP_82758681887197562725795312046, phi_seventyBP_82758681887197562725795312047,
    phi_seventyBP_82758681887197562725795312048, phi_seventyBP_82758681887197562725795312049, phi_seventyBP_82758681887197562725795312050,
    phi_seventyBP_82758681887197562725795312051, phi_seventyBP_82758681887197562725795312052, phi_seventyBP_82758681887197562725795312053,
    phi_seventyBP_82758681887197562725795312054, phi_seventyBP_82758681887197562725795312055, phi_seventyBP_82758681887197562725795312056,
    phi_seventyBP_82758681887197562725795312057, phi_seventyBP_82758681887197562725795312058, phi_seventyBP_82758681887197562725795312059,
    phi_seventyBP_82758681887197562725795312060, phi_seventyBP_82758681887197562725795312061, phi_seventyBP_82758681887197562725795312062,
    phi_seventyBP_82758681887197562725795312063, phi_seventyBP_82758681887197562725795312064, phi_seventyBP_82758681887197562725795312065,
    phi_seventyBP_82758681887197562725795312066, phi_seventyBP_82758681887197562725795312067, phi_seventyBP_82758681887197562725795312068,
    phi_seventyBP_82758681887197562725795312069, phi_seventyBP_82758681887197562725795312070, phi_seventyBP_82758681887197562725795312071,
    phi_seventyBP_82758681887197562725795312072, phi_seventyBP_82758681887197562725795312073, phi_seventyBP_82758681887197562725795312074,
    phi_seventyBP_82758681887197562725795312075, phi_seventyBP_82758681887197562725795312076, phi_seventyBP_82758681887197562725795312077,
    phi_seventyBP_82758681887197562725795312078, phi_seventyBP_82758681887197562725795312079, phi_seventyBP_82758681887197562725795312080,
    phi_seventyBP_82758681887197562725795312081, phi_seventyBP_82758681887197562725795312082, phi_seventyBP_82758681887197562725795312083,
    phi_seventyBP_82758681887197562725795312084, phi_seventyBP_82758681887197562725795312085, phi_seventyBP_82758681887197562725795312086,
    phi_seventyBP_82758681887197562725795312087, phi_seventyBP_82758681887197562725795312088, phi_seventyBP_82758681887197562725795312089,
    phi_seventyBP_82758681887197562725795312090, phi_seventyBP_82758681887197562725795312091, phi_seventyBP_82758681887197562725795312092,
    phi_seventyBP_82758681887197562725795312093, phi_seventyBP_82758681887197562725795312094, phi_seventyBP_82758681887197562725795312095,
    phi_seventyBP_82758681887197562725795312096, phi_seventyBP_82758681887197562725795312097, phi_seventyBP_82758681887197562725795312098,
    phi_seventyBP_82758681887197562725795312099, phi_seventyBP_82758681887197562725795312100, phi_seventyBP_82758681887197562725795312101]

end TotientTailPeriodKiller
end Erdos249257
